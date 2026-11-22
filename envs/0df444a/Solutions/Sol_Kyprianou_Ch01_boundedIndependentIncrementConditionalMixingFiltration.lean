-- Prove2me | solution 1 for Kyprianou.Ch01.boundedIndependentIncrementConditionalMixingFiltration
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:50:06.289476+00:00
-- url     : https://prove2.me/submissions/71f6cefa-628e-4a96-9cc1-aca05b862e5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_mckeanRightMixingRegularityV1
import Theorems.Thm_Kyprianou_Ch01_mckeanRightMixingSetIntegralV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (s : ℝ≥0)
    (Y Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hYm : @Measurable Ω ℝ (F s) inferInstance Y)
    (hZm : Measurable Z)
    (hf : Measurable f)
    (hBound : ∀ y, ‖f y‖ ≤ K)
    (hIndep : Indep (MeasurableSpace.comap Z inferInstance) (F s) P) :
    P[(fun ω => f (Y ω + Z ω)) | F s] =ᵐ[P]
      (fun ω => ∫ ξ, f (Y ω + Z ξ) ∂P) := by
  have hreg :=
    Kyprianou.Ch01.mckeanRightMixingRegularityV1
      P F s Y Z f K hYm hZm hf hBound hIndep
  rcases hreg with ⟨hfint, hgint, hgm⟩
  have hset :=
    Kyprianou.Ch01.mckeanRightMixingSetIntegralV1
      P F s Y Z f K hYm hZm hf hBound hIndep
  have hcond := ae_eq_condExp_of_forall_setIntegral_eq
    (F.le s) hfint
    (fun A _ _ => hgint.integrableOn)
    (fun A hA _ => (hset A hA).symm)
    hgm
  exact hcond.symm
