-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_initial_cell_ucp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:49:24.384089+00:00
-- url     : https://prove2.me/submissions/e5d0b194-4302-434f-ba23-7bdb3dcd2d4a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_Kyprianou_Ch04_ito43_small_time_increment_envelope
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A measurable envelope for the short-time oscillation of a cadlag path. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P) (C : ℝ) (T : NNReal) :
    ∀ e : ℝ, 0 < e → Tendsto (fun n : ℕ =>
      (P {w | ∃ t ≤ T, e ≤ |C * (X (min t (T / (n : NNReal))) w - X 0 w)|}).toReal)
      atTop (nhds 0) := by
  intro e he
  obtain ⟨Y,hY,heq,hCad⟩ := Kyprianou.Ch04.ito43_levy_joint_version P X hX
  obtain ⟨B,hB,hlim,hbound⟩ := Kyprianou.Ch04.ito43_small_time_increment_envelope Y hY hCad T
  let E : ℕ → NNReal → Ω → ℝ := fun n t w =>
    C * (X (min t (T / (n : NNReal))) w - X 0 w)
  let D : ℕ → Ω → ℝ := fun n w => |C| * B n w
  have hDm (n : ℕ) : AEStronglyMeasurable (D n) P :=
    (measurable_const.mul (hB n)).aestronglyMeasurable
  have hDl : ∀ᵐ w ∂P, Tendsto (fun n => D n w) atTop (nhds 0) := by
    filter_upwards [] with w
    simpa only [mul_zero] using (tendsto_const_nhds (x := |C|)).mul (hlim w)
  have hDb : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |E n t w| ≤ |D n w| := by
    filter_upwards [heq] with w hw
    intro n t ht
    change |C * (X (min t (T / (n : NNReal))) w - X 0 w)| ≤ |D n w|
    rw [← hw (min t (T / (n : NNReal))), ← hw 0, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hbound n w _ (min_le_right _ _)) (abs_nonneg C)).trans
      (le_abs_self _)
  exact Kyprianou.Ch04.ito43_ucp_countable_envelope P E D T hDm hDl hDb e he
