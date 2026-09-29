-- Prove2me | solution 1 for HorizontalPadicL.seededHorizontalPadicLFunction_assemble_v4
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:58:19.782224+00:00
-- url     : https://prove2.me/submissions/d5ae83c7-34b2-4089-b92c-5be1f3291c2c

import Definitions.Def_KN_InverseSeedConventionV2
import Definitions.Def_KN_SeededHorizontalPadicLFunctionV3B
import Definitions.Def_KN_SeededThetaConstructionV2B

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B)
    (μ : SeededNormalizedThetaMeasureV3 L.toConstructionData)
    (hcharacters : μ.characters.HasExpectedProperties)
    (hinterp : μ.InterpolatesSeededCriticalValues)
    (htrivial : μ.measure.eval
      (trivialHorizontalCharacterV2 p L.toConstructionData.exponent) ≠ 0) :
    ∃ ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η,
      ν.primes = L ∧ ν.InterpolatesSeededCriticalValuesV4 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0 := by
  let ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η :=
    { primes := L
      coefficientRing := μ.coefficientRing
      coefficient_integral := μ.coefficient_integral
      measure := μ.measure }
  refine ⟨ν, rfl, ?_, htrivial⟩
  refine ⟨μ.characters, hcharacters, ?_⟩
  intro χ
  exact hinterp χ
