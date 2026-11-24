-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallJumpKernelIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:46:58.402692+00:00
-- url     : https://prove2.me/submissions/5a0b8d52-2822-4b5a-82ec-645df00a3ae1

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpSquareIntegrableV1
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpRemainderPointwiseV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (b : Real) :
    IntegrableOn (fun x : Real => Real.exp (b * x) - 1 - b * x)
      (Set.Ioo (-1 : Real) 1) T.levyMeasure := by
  let m := T.levyMeasure.restrict (Set.Ioo (-1 : ℝ) 1)
  let C := Real.exp |b| + 1 + |b| + 1
  have hsq := Kyprianou.Ch03.momentSmallJumpSquareIntegrableV1 T
  have hm : ∀ᵐ x ∂m, x ∈ Set.Ioo (-1 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  change Integrable (fun x : ℝ => Real.exp (b*x)-1-b*x) m
  apply (hsq.const_mul (C*b^2)).mono (by fun_prop)
  filter_upwards [hm] with x hx
  have hh := Kyprianou.Ch03.momentSmallJumpRemainderPointwiseV1 b x (abs_le.mpr ⟨hx.1.le,hx.2.le⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ C*b^2*x^2 by dsimp [C]; positivity)] using hh
