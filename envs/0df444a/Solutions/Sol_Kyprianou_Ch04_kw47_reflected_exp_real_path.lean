-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_reflected_exp_real_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:13:39.27902+00:00
-- url     : https://prove2.me/submissions/870f4676-c316-43b1-a6b0-bcf8e6512fd5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The reflected exponential has bounded measurable right-continuous
paths after extending nonnegative time by the zero-time value. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) :
    let Z : Real → Real := fun r =>
      Real.exp (-alpha * (runningSup L r.toNNReal w - L.X r.toNNReal w))
    Measurable Z ∧ (∀ r, ‖Z r‖ ≤ 1) ∧
      ∀ r, ContinuousWithinAt Z (Ici r) r := by
  dsimp only
  let Z : NNReal → Real := fun r =>
    Real.exp (-alpha * (runningSup L r w - L.X r w))
  have hU := levy_runningSup_joint_time_path_measurable L
  have hX := chat04_levy_joint_time_state_measurable L
  have hMap : Measurable (fun r : NNReal => (r,w)) :=
    measurable_id.prodMk measurable_const
  have hUZ := hU.comp hMap
  have hXZ := hX.comp hMap
  have hm : Measurable Z := by
    exact (measurable_const.mul (hUZ.sub hXZ)).exp
  refine ⟨hm.comp measurable_real_toNNReal, ?_, ?_⟩
  · intro r
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Kyprianou.Ch04.kw47_reflected_exp_bounds
      L alpha hAlpha r.toNNReal w).2
  · intro r
    have hUcont := (runningSup_continuous_actual L w).continuousWithinAt
      (s := Ici r.toNNReal) (x := r.toNNReal)
    have hterm : ContinuousWithinAt
      (fun s : NNReal => -alpha * (runningSup L s w - L.X s w))
        (Ici r.toNNReal) r.toNNReal :=
      continuousWithinAt_const.mul (hUcont.sub (L.rightCont w r.toNNReal))
    have hz : ContinuousWithinAt Z (Ici r.toNNReal) r.toNNReal := hterm.rexp
    have hmap : MapsTo Real.toNNReal (Ici r) (Ici r.toNNReal) :=
      fun x hx => Real.toNNReal_le_toNNReal hx
    exact hz.comp continuous_real_toNNReal.continuousWithinAt hmap
