-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallJumpSquareIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:01.618176+00:00
-- url     : https://prove2.me/submissions/759d3464-1c61-4c5d-b2fc-9126c4256ced

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) :
    IntegrableOn (fun x : Real => x ^ 2) (Set.Ioo (-1 : Real) 1) T.levyMeasure := by
  let m := T.levyMeasure.restrict (Set.Ioo (-1 : ℝ) 1)
  have hm : ∀ᵐ x ∂m, x ∈ Set.Ioo (-1 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  have hmin : Integrable (fun x : ℝ => min 1 (x ^ 2)) T.levyMeasure := by
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
      (fun x : ℝ => le_min (by norm_num) (sq_nonneg x)))).mpr ?_⟩
    exact T.levyMeasure_isLevyMeasure.2
  change Integrable (fun x : ℝ => x ^ 2) m
  apply (hmin.mono_measure Measure.restrict_le_self).mono (by fun_prop)
  filter_upwards [hm] with x hx
  have hx' : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le,hx.2.le⟩
  have hx2 : x ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg x) hx' 2
    simpa only [sq_abs, one_pow] using h
  simp [min_eq_right hx2]
