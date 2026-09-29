-- Prove2me | solution 1 for ModularCurve.heckeInputsAllTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5ed84704-b8af-5919-9e91-6092b796e7e3

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeInputsAllTranspose
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve~separableAlong_of_charZero ModularCurve"

namespace W7ATranspose

theorem separableAlong_of_charZero {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [CharZero F] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  letI := algebraAlong φ
  haveI : Algebra.IsIntegral F F' := ⟨fun x => hφ x⟩
  show Algebra.IsSeparable F F'
  infer_instance

end W7ATranspose

theorem solution (N : ℕ) [NeZero N] (ℓ : Nat.Primes) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∃ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
      (_ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)),
      FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα ∧
        NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hfin := by
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  obtain ⟨hα, hβ, hP, hfinα, -, -⟩ :=
    ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) N (ℓ : ℕ)
  have hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) :=
    ModularCurve.finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N ℓ
  refine ⟨hα, hβ, hP, hfinβ, ?_, ?_⟩
  · exact AlgebraicCurve.fundamentalIdentityAlong _ hα hfinα
      (W7ATranspose.separableAlong_of_charZero _ hα)
  · exact AlgebraicCurve.normFormulaAlong _ hfinβ
      (W7ATranspose.separableAlong_of_charZero _ hβ)

end S_ModularCurve_heckeInputsAllTranspose
end P2MW
export P2MW.S_ModularCurve_heckeInputsAllTranspose (solution)
