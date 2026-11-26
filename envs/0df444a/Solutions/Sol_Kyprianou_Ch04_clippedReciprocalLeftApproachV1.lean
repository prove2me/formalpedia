-- Prove2me | solution 1 for Kyprianou.Ch04.clippedReciprocalLeftApproachV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:57:08.887954+00:00
-- url     : https://prove2.me/submissions/41317748-f16e-4cf3-ae0e-46d3025e87c3

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The clipped reciprocal approximations approach a positive time strictly from the left. -/
theorem solution (t : NNReal) (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.toNNReal ((t : ℝ) - 1 / ((n : ℝ) + 1)))
      atTop (𝓝[<] t) := by
  let r (n : ℕ) (t : NNReal) := Real.toNNReal ((t : ℝ) - 1 / ((n : ℝ) + 1))
  have hlim : Tendsto (fun n : ℕ => r n t) atTop (𝓝 t) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp hn)
    have h := (tendsto_const_nhds (x := (t : ℝ))).sub h0
    apply NNReal.tendsto_coe.mp
    simpa [r, Real.coe_toNNReal', max_eq_left t.coe_nonneg, max_eq_right t.coe_nonneg] using
      (h.max (tendsto_const_nhds (x := (0 : ℝ))))
  have hwithin : Tendsto (fun n : ℕ => r n t) atTop (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim, Eventually.of_forall fun n => ?_⟩
    change r n t < t
    apply NNReal.coe_lt_coe.mp
    dsimp [r]
    exact max_lt (sub_lt_self _ (by positivity)) (by positivity : 0 < (t : ℝ))
  exact hwithin
