-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0cc38faa-eec8-57bd-b4f0-b811ca7d10ec

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval

set_option autoImplicit false

open Polynomial LanglandsTunnell.RankinSelberg

theorem solution
    (q : ℝ) (hq : 0 < q) (a b : ℂ) (hb : b ≠ 0) (hnorm : ‖b‖ = q)
    (hconj : (starRingEnd ℂ) a * b = (q : ℂ) * a) (X : ℂ) :
    (rsEulerPoly (a / q) (b / q ^ 2) ((starRingEnd ℂ) a / q) ((starRingEnd ℂ) b / q ^ 2) 0).eval ((q : ℂ) * X) =
      (rsEulerPoly (a / b) b⁻¹ a b 0).eval X := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'

  have hbb : b * (starRingEnd ℂ) b = (q : ℂ) ^ 2 := by
    rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj, ← hnorm, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hcb : (starRingEnd ℂ) b = (q : ℂ) ^ 2 / b := by
    field_simp
    rw [mul_comm] at hbb
    exact hbb
  have hca : (starRingEnd ℂ) a = (q : ℂ) * a / b := by
    field_simp
    exact hconj
  simp only [rsEulerPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, hcb, hca]
  field_simp
  ring

end S_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval (solution)
