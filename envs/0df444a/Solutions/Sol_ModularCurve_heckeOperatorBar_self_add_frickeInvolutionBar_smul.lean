-- Prove2me | solution 1 for ModularCurve.heckeOperatorBar_self_add_frickeInvolutionBar_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8bc02f9a-e6c2-543e-a7de-0fa9da230e4c

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_isPrincipal_of_degree_eq_zero_charLOne
import Theorems.Thm_AlgebraicCurve_Pic0_forall_isPrincipal_of_ringEquiv
import Theorems.Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff
import Theorems.Thm_ModularCurve_heckeDivBar_self_add_frickeInvolutionBar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorBar_self_add_frickeInvolutionBar_smul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
open ModularCurve AlgebraicCurve

private theorem bar_one_eq_C_one :
    modularFunctionFieldBar 1 = modularFunctionFieldC (AlgebraicClosure ℚ) 1 :=
  laurentBaseChange_adjoin_pair (AlgebraicClosure ℚ) 1 functionFieldGeneration_one

private theorem isPrincipal_of_degree_eq_zero_bar_one
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar 1))
    (hD : Divisor.degree D = 0) : D.IsPrincipal := by
  have e : (modularFunctionFieldC (AlgebraicClosure ℚ) 1 : IntermediateField _ _)
      ≃ₐ[AlgebraicClosure ℚ] (modularFunctionFieldBar 1 : IntermediateField _ _) :=
    IntermediateField.equivOfEq bar_one_eq_C_one.symm
  exact Pic0.forall_isPrincipal_of_ringEquiv e.toRingEquiv
    (fun a => e.commutes a) (fun D' hD' => isPrincipal_of_degree_eq_zero_charLOne D' hD') D hD

private theorem hA_row (p : ℕ) [Fact p.Prime]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * p)))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (hι : (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)).toRingHom.IsIntegral)
    (hσ : (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)).toRingHom.IsIntegral)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) :
    Divisor.correspondence (heckeBetaBar (AlgebraicClosure ℚ) p p)
        (heckeAlphaBar (AlgebraicClosure ℚ) p p) hβ hα D
      + frickeInvolutionBar p • D
    = Divisor.pullbackAlong (towerSubstBar (AlgebraicClosure ℚ) 1 p ((one_mul p).dvd)) hσ
        (Divisor.pushforwardAlong (towerInclBar (AlgebraicClosure ℚ) (one_dvd p)) hι D) := by
  exact ModularCurve.heckeDivBar_self_add_frickeInvolutionBar_smul p hα hβ hι hσ D

namespace JmatchAux1

private theorem assembly {K F F' F₁ : Type*} [Field K] [Field F] [Field F'] [Field F₁]
    [Algebra K F] [Algebra K F'] [Algebra K F₁]
    [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F]
    {φ ψ : F →ₐ[K] F'} {hφ : φ.toRingHom.IsIntegral} {hψ : ψ.toRingHom.IsIntegral}
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin)
    {w : F ≃ₐ[K] F}
    {ι σ : F₁ →ₐ[K] F} {hι : ι.toRingHom.IsIntegral} {hσ : σ.toRingHom.IsIntegral}
    (hA : ∀ D : Divisor K F, Divisor.correspondence φ ψ hφ hψ D + w • D =
        Divisor.pullbackAlong σ hσ (Divisor.pushforwardAlong ι hι D))
    (hprin : ∀ E : Divisor K F₁, Divisor.degree E = 0 → E.IsPrincipal)
    (x : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN x + w • x = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.smul_mk, ← Pic0.mk_add, Pic0.mk_eq_zero_iff,
    AddSubgroup.coe_add, Pic0.coe_degZeroCorrespondence, Pic0.coe_degZeroSMulHom, hA]
  refine Divisor.isPrincipal_pullbackAlong σ hσ (hprin _ ?_)
  rw [Divisor.degree_pushforwardAlong]
  exact Divisor.mem_degZero.mp D.2

end JmatchAux1

theorem solution (p : ℕ)
    [Fact p.Prime] :
    ∀ x : JZero p, heckeOperatorBar p ⟨p, Fact.out⟩ x + frickeInvolutionBar p • x = 0 := by
  intro x
  show heckeOperatorAlong (AlgebraicClosure ℚ) p p x + frickeInvolutionBar p • x = 0
  obtain ⟨hα, hβ, hP, hfin, hFI, hN⟩ :=
    heckeInputsAlong_of_prime (AlgebraicClosure ℚ) p p
  haveI := hP
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional p
  rw [heckeOperatorAlong_eq hα hβ hFI hfin hN]
  exact JmatchAux1.assembly hFI hfin hN
    (hA_row p hα hβ
      (towerInclBar_isIntegral (AlgebraicClosure ℚ) (one_dvd p))
      (towerSubstBar_isIntegral (AlgebraicClosure ℚ) p ((one_mul p).dvd)))
    isPrincipal_of_degree_eq_zero_bar_one x

end S_ModularCurve_heckeOperatorBar_self_add_frickeInvolutionBar_smul
end P2MW
export P2MW.S_ModularCurve_heckeOperatorBar_self_add_frickeInvolutionBar_smul (solution)
