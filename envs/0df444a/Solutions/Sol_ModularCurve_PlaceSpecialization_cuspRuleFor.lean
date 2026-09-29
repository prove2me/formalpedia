-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.cuspRuleFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4937ad4b-76c7-548d-8f53-0173956d65cb

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Theorems.Thm_ModularCurve_PlaceSpecialization_cuspRuleStrongFor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_cuspRuleFor
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ p : ℕ) [Fact ℓ.Prime] [NeZero p] (hp : p.Prime) (hℓp : ℓ ≠ p)
    (data : ModularCurve.ModularPolynomialData ℓ) (hKr : ModularCurve.KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (S : ModularCurve.PlaceSpecialization A ℓ p data hKr k red hα hβ)
    [Module ModularCurve.HeckeAlg (ModularCurve.JZero p)] :
    ModularCurve.CuspRuleFor A S.spPic0 := by
  intro x j₁ j₂ hinf hzero hfix h1 h2 hv
  obtain ⟨ha, hb⟩ :=
    ModularCurve.PlaceSpecialization.cuspRuleStrongFor A ℓ p hp hℓp data hKr k red hα hβ S
      x j₁ j₂ hinf hzero hfix h1 h2 hv
  exact ⟨fun hh => by rw [ha hh]; exact zero_mem _, fun hh => by rw [hb hh]; exact zero_mem _⟩

end S_ModularCurve_PlaceSpecialization_cuspRuleFor
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_cuspRuleFor (solution)
