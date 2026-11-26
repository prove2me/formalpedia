-- Prove2me | solution 1 for NCGchk.schwarzschild_log_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:41:46.709412+00:00
-- url     : https://prove2.me/submissions/d30fd33f-47a8-4d3c-8486-fd02d66a04bd

import Mathlib
namespace NCGchk
theorem _root_.solution :
    (257 / 302 : ℝ) / (2 * (1 - (257 / 302 : ℝ))) - 1 / 2 = 106 / 45 := by
  norm_num

end NCGchk
