-- Prove2me | solution 1 for Kyprianou.Ch03.stableLevyLogMomentTimeScalingV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:04:29.291569+00:00
-- url     : https://prove2.me/submissions/893e53d7-b38f-48c4-ba4d-6c35a081f1f4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_stableLevyExtendedMomentMulV1
import Theorems.Thm_Kyprianou_Ch03_stableLevyMomentRightFatouV1
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scalar_moment_exp
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (b : ℝ) (hi : ∀ t, Integrable (fun w => Real.exp (b * X t w)) P)
    (t : NNReal) :
    Real.log (∫ w, Real.exp (b * X t w) ∂P) =
      (t : ℝ) * Real.log (∫ w, Real.exp (b * X 1 w) ∂P) := by
  let G : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ w, ENNReal.ofReal (Real.exp (b * X s w)) ∂P
  have hmeas (s : ℝ≥0) : AEMeasurable (fun w => Real.exp (b * X s w)) P :=
    Real.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX s))
  have hne (s : ℝ≥0) : G s ≠ 0 := by
    intro hs
    obtain ⟨w, hw⟩ := ((lintegral_eq_zero_iff' (ENNReal.measurable_ofReal.comp_aemeasurable
      (hmeas s))).1 hs).exists
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hw
  have hG0 : G 0 = 1 := by simp [G, hX.start_zero]
  have hMul := Kyprianou.Ch03.stableLevyExtendedMomentMulV1 X hX b
  have hfin (s : ℝ≥0) : G s ≠ ⊤ := (hi s).lintegral_lt_top.ne
  have hReal (s : ℝ≥0) :
      (∫ w, Real.exp (b * X s w) ∂P) = (G s).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun w => (Real.exp_pos _).le) (hmeas s).aestronglyMeasurable
  have he := Kyprianou.Ch08.StageB.source_result81_scalar_moment_exp G hG0 hMul hne hfin
    (Kyprianou.Ch03.stableLevyMomentRightFatouV1 X hX b) t
  rw [hReal 1, hReal t, he, Real.log_exp]
