-- Prove2me | solution 1 for Kyprianou.Ch04.runningInfimumExpRewardProperties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:43.648724+00:00
-- url     : https://prove2.me/submissions/08dbb44c-643f-42ca-b6a0-6a6870cfdab5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Theorems.Thm_Kyprianou_Ch04_runningInfimumAntitoneFromFiniteBounds
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Exponentiating the finite-horizon running infimum gives a bounded decreasing reward. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (beta : ℝ) (hb : 0 < beta) :
    let g : NNReal × Ω → ℝ := fun z =>
      Real.exp (beta * sInf ((fun s : NNReal => L.X s z.2) '' Iic z.1))
    Measurable g ∧ (∀ z, 0 ≤ g z) ∧ (∀ z, g z ≤ 1) ∧
      ∀ w, Antitone (fun t : NNReal => g (t,w)) := by
  intro g
  have hs (t : NNReal) (w : Ω) : ((fun s : NNReal => L.X s w) '' Iic t) =
      {y : ℝ | ∃ s : NNReal, s ≤ t ∧ y = L.X s w} := by
    ext y
    constructor <;> rintro ⟨s,hs,he⟩ <;> exact ⟨s,hs,he.symm⟩
  have hbdd (t : NNReal) (w : Ω) : BddBelow ((fun s : NNReal => L.X s w) '' Iic t) := by
    rw [hs]
    exact levy_path_bddBelow_finite_horizon L t w
  have hi : Measurable (fun z : NNReal × Ω => sInf ((fun s : NNReal => L.X s z.2) '' Iic z.1)) := by
    have h := (levy_running_infimum_joint_time_path_measurable L).neg
    change Measurable (fun z : NNReal × Ω => -(-sInf {y : ℝ | ∃ s : NNReal, s ≤ z.1 ∧ y = L.X s z.2})) at h
    simpa only [neg_neg, hs] using h
  refine ⟨(measurable_const.mul hi).exp, fun z => (Real.exp_pos _).le, ?_, ?_⟩
  · intro z
    have hz := csInf_le (hbdd z.1 z.2)
      (show L.X 0 z.2 ∈ ((fun s : NNReal => L.X s z.2) '' Iic z.1) from ⟨0, by simp, rfl⟩)
    rw [L.X_zero] at hz
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hb.le hz)
  · intro w
    have ha := Kyprianou.Ch04.runningInfimumAntitoneFromFiniteBounds
      (fun t => L.X t w) (fun t => hbdd t w)
    intro t u htu
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ha htu) hb.le)
