-- Prove2me | solution 1 for ModularCurve.qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/dbf05107-892f-5f8b-acb8-5092478228d7

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFrobeniusModL qExpFrobeniusModL_isIntegral qExpFrobeniusPlaceModL qExpFrobeniusDivPushforwardModL qExpFrobeniusDivPushforwardModL_single coe_qExpFrobeniusDegZeroPushforwardModL qExpFrobeniusPushforwardModL qExpFrobeniusPushforwardModL_mk qExpFunctionFieldC qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental"
namespace FDivSol
p2m_open "ModularCurve"

variable {K : Type*} [Field K] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} {p : ℕ} [Fact p.Prime] [CharP K p]

theorem inertiaDegAlong_frob_eq_one [IsAlgClosed K] [IsCurveOver K (qExpFunctionFieldC K Γ)]
    (w : Place K (qExpFunctionFieldC K Γ)) :
    w.inertiaDegAlong (qExpFrobeniusModL K Γ p) (qExpFrobeniusModL_isIntegral K Γ p) = 1 := by
  letI := algebraAlong (qExpFrobeniusModL K Γ p)
  haveI := isScalarTower_along (qExpFrobeniusModL K Γ p)
  haveI := isIntegral_along (qExpFrobeniusModL K Γ p) (qExpFrobeniusModL_isIntegral K Γ p)
  have h := Place.deg_restrict_mul_inertiaDeg (F := qExpFunctionFieldC K Γ) w
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem qExpFrobeniusDivPushforwardModL_eq_mapDomain [IsAlgClosed K] [IsCurveOver K (qExpFunctionFieldC K Γ)]
    (D : Divisor K (qExpFunctionFieldC K Γ)) :
    qExpFrobeniusDivPushforwardModL K Γ p D = Finsupp.mapDomain (qExpFrobeniusPlaceModL K Γ p) D := by
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.mapDomain_zero]
  | add a b ha hb => rw [map_add, Finsupp.mapDomain_add, ha, hb]
  | single w n =>
    rw [qExpFrobeniusDivPushforwardModL_single, inertiaDegAlong_frob_eq_one, Nat.cast_one, mul_one,
      Finsupp.mapDomain_single]

end ModularCurve.FDivSol

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hx : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (F : Pic0 K (ModularCurve.qExpFunctionFieldC K Γ) →+ Pic0 K (ModularCurve.qExpFunctionFieldC K Γ))
    (hF : ∀ z, F z = ModularCurve.qExpFrobeniusPushforwardModL K Γ p z)
    (Φ : Place K (ModularCurve.qExpFunctionFieldC K Γ) ≃ Place K (ModularCurve.qExpFunctionFieldC K Γ))
    (hΦ : ∀ v, Φ v = ModularCurve.qExpFrobeniusPlaceModL K Γ p v) :
    ∀ (D D' : Divisor.degZero (K := K) (F := ModularCurve.qExpFunctionFieldC K Γ)),
      (D' : Divisor K (ModularCurve.qExpFunctionFieldC K Γ)) =
        Finsupp.mapDomain Φ (D : Divisor K (ModularCurve.qExpFunctionFieldC K Γ)) →
      F (Pic0.mk D) = Pic0.mk D' := by
  intro D D' hD'
  haveI := IsAlgClosed.perfectField K
  obtain ⟨x, htr, hfd⟩ := hx
  haveI : IsCurveOver K (ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  obtain ⟨hin, -⟩ :=
    ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental K (ℓ := p) Γ ⟨x, htr, hfd⟩
  obtain ⟨hP, hfin, hFI, hN⟩ := hin
  haveI := hP
  rw [hF, ModularCurve.qExpFrobeniusPushforwardModL_mk hfin hFI hN]
  congr 1
  apply Subtype.ext
  rw [ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL, hD',
    ModularCurve.FDivSol.qExpFrobeniusDivPushforwardModL_eq_mapDomain]
  congr 1
  exact (funext hΦ).symm

end S_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain
end P2MW
export P2MW.S_ModularCurve_qExpFrobeniusPushforwardModL_mk_eq_mk_of_eq_mapDomain (solution)
