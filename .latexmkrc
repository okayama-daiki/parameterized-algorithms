$pdf_mode = 3;

$latex = 'lualatex -synctex=1 -halt-on-error -interaction=nonstopmode -file-line-error %O %S';
$bibtex = 'biber %O %B';
$dvipdf = 'dvipdfmx %O -o %D %S';
$makeindex = 'mendex %O -o %D %S';

$out_dir = 'dist';
$aux_dir = '.tex';
