-- Prove2me | solution 1 for MovingMediaOptics.Gordon.eq_33_null_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:25:59.512004+00:00
-- url     : https://prove2.me/submissions/04864c11-bf92-498d-8363-c6df44e42acb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

open QAlgorithms.Papers.Independent.Renew46.P42
open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem solution (c n : ℝ) (u k : V3) (omega : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    c ^ 2 * quadratic (gUp c n u) (waveCovector c omega k) =
      rayDispersion c n u k omega := by
  have hc0 : c ≠ 0 := hc.ne'
  simp only [quadratic, gUp, minkowskiMetric, fourFlow, waveCovector, rayDispersion, dot3,
    Fin.sum_univ_four, Fin.sum_univ_three]
  simp
  field_simp
  ring
