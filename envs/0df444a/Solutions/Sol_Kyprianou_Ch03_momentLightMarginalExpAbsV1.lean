-- Prove2me | solution 1 for Kyprianou.Ch03.momentLightMarginalExpAbsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:35:56.165844+00:00
-- url     : https://prove2.me/submissions/7b4a4b75-7b97-46a7-a8cf-b98af352a63d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentSmallGaussianMarginalFiniteApproxV1
import Theorems.Thm_Kyprianou_Ch03_momentUniformExpBoundOfCharLimitV1
import Theorems.Thm_Kyprianou_Ch03_momentSignedExpToAbsExpV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (ht : 0 < t)
    (nu : Measure Real) [IsProbabilityMeasure nu]
    (hnu : ∀ xi : Real, charFun nu xi = Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((T.drift * xi : Real) : Complex) -
          (((T.gaussianVariance : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x in Set.Ioo (-1 : Real) 1,
            ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure)))
    (b : Real) (hb : 0 < b) :
    Integrable (fun x : Real => Real.exp (b * |x|)) nu := by
  obtain ⟨q, hq, hbnd⟩ :=
    Kyprianou.Ch03.momentSmallGaussianMarginalFiniteApproxV1 T t ht
  let nu' : ProbabilityMeasure ℝ := ⟨nu, inferInstance⟩
  have hconv (xi : ℝ) : Tendsto (fun n => charFun (q n : Measure ℝ) xi) atTop
      (𝓝 (charFun (nu' : Measure ℝ) xi)) := by
    change Tendsto _ _ (𝓝 (charFun nu xi))
    rw [hnu xi]
    exact hq xi
  have hm (c : ℝ) : Integrable (fun x : ℝ => Real.exp (c * x)) nu := by
    obtain ⟨C, hC, hbound⟩ := hbnd c
    exact Kyprianou.Ch03.momentUniformExpBoundOfCharLimitV1 q nu' hconv c C hC hbound
  exact Kyprianou.Ch03.momentSignedExpToAbsExpV1 nu b (hm b) (hm (-b))
