-- Prove2me | solution 1 for NoHair.reissnerNordstrom_lapse_of_radial_equation
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:51:48.967951+00:00
-- url     : https://prove2.me/submissions/338bba36-026e-479d-b38f-d9e65c1e3184

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Set

theorem solution (R e : ℝ) (A : ℝ → ℝ)
    (hR : 0 < R) (hA : ContinuousOn A (Ici R)) (horizon : A R = 0)
    (hpos : ∀ r, R < r → 0 < A r)
    (hrad : ∀ r, R < r → HasDerivAt (fun s => s * (1 - A s)) (e ^ 2 / r ^ 2) r) :
    ∃ m : ℝ, 0 < m ∧ e ^ 2 ≤ m ^ 2 ∧ R = m + Real.sqrt (m ^ 2 - e ^ 2) ∧
      ∀ r, R < r → r ^ 2 * (1 - A r) = 2 * m * r - e ^ 2 := by
  let K (r : ℝ) := r * (1 - A r) + e ^ 2 / r
  have hK (x : ℝ) (hx : R < x) : HasDerivAt K 0 x := by
    have hdiv := (hasDerivAt_const x (e ^ 2)).div (hasDerivAt_id x) (lt_trans hR hx).ne'
    convert (hrad x hx).add hdiv using 1
    all_goals first | rfl | (simp only [id_eq]; ring)
  let m := (R + e ^ 2 / R) / 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hKR : K R = 2 * m := by simp [K, m, horizon]; ring
  have hprofile (r : ℝ) (hr : R < r) : r ^ 2 * (1 - A r) = 2 * m * r - e ^ 2 := by
    have hsub : Icc R r ⊆ Ici R := fun _ hx => hx.1
    have hc : ContinuousOn K (Icc R r) :=
      (continuousOn_id.mul (continuousOn_const.sub (hA.mono hsub))).add
        (continuousOn_const.div continuousOn_id (fun _ hx => (lt_of_lt_of_le hR hx.1).ne'))
    obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope K (fun _ => 0) hr hc
      (fun x hx => hK x hx.1)
    have hconst : K r = K R := by
      have := (eq_div_iff (sub_ne_zero.mpr hr.ne')).mp hslope
      linarith
    calc
      r ^ 2 * (1 - A r) = K r * r - e ^ 2 := by
        dsimp [K]
        field_simp [(lt_trans hR hr).ne']
        ring
      _ = 2 * m * r - e ^ 2 := by rw [hconst, hKR]
  have hroot : R ^ 2 - 2 * m * R + e ^ 2 = 0 := by
    dsimp [m]
    field_simp [hR.ne']
    ring
  have hdisc : m ^ 2 - e ^ 2 = (R - m) ^ 2 := by nlinarith only [hroot]
  have hRm : m ≤ R := by
    by_contra! hlt
    have hpositive := mul_pos (sq_pos_of_pos hm) (hpos m hlt)
    nlinarith only [hpositive, hprofile m hlt, hdisc, sq_nonneg (R - m)]
  refine ⟨m, hm, by nlinarith only [hdisc, sq_nonneg (R - m)], ?_, hprofile⟩
  rw [hdisc, Real.sqrt_sq (sub_nonneg.mpr hRm)]
  ring
