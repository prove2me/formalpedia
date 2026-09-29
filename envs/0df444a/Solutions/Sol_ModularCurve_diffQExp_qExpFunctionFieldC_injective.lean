-- Prove2me | solution 1 for ModularCurve.diffQExp_qExpFunctionFieldC_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3ff1fd65-837b-53cb-b1ff-67c8bf76a231

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diffQExp_qExpFunctionFieldC_injective
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~coeff_jqModC_neg_one AlgebraicCurve HahnSeries"

namespace DiffQExpInj

theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have hZ : (jqModC ℤ).coeff (-1) = 1 := by
    have h := congrArg (fun s : LaurentSeries ℚ => s.coeff (-1)) (jqModC_eq_map_intCast ℚ)
    simp only [HahnSeries.map_coeff, jqModC_rat, coeff_jq_neg_one, eq_intCast] at h
    exact_mod_cast h.symm
  rw [jqModC_eq_map_intCast K, HahnSeries.map_coeff, hZ, map_one]

theorem qEuler_jqModC_ne_zero (K : Type*) [Field K] : qEuler K (jqModC K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  simp only [qEuler_coeff, coeff_jqModC_neg_one, mul_one, Int.cast_neg, Int.cast_one,
    HahnSeries.coeff_zero, neg_eq_zero, one_ne_zero] at h1

end DiffQExpInj

open DiffQExpInj in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ)) := by
  let F : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K Γ
  obtain ⟨x, hxj, hxt, hfd⟩ :
      ∃ x : F, (x : LaurentSeries K) = jqModC K ∧ Transcendental K x ∧
        FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : IsCurveOver K F :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hfd
  have hrank : Module.finrank F Ω[F⁄K] = 1 :=
    AlgebraicCurve.IsCurveOver.finrank_kaehler (K := K) (F := F)

  have hD : diffQExp F (KaehlerDifferential.D K F x) ≠ 0 := by
    rw [diffQExp_D]
    rw [hxj]
    exact qEuler_jqModC_ne_zero K
  have hD0 : KaehlerDifferential.D K F x ≠ 0 := fun h => hD (by rw [h, map_zero])

  have hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F x = ω :=
    (finrank_eq_one_iff_of_nonzero' (KaehlerDifferential.D K F x) hD0).mp hrank
  show Function.Injective (diffQExp F)
  intro ω₁ ω₂ h
  rw [← sub_eq_zero] at h ⊢
  rw [← map_sub] at h
  obtain ⟨c, hc⟩ := hspan (ω₁ - ω₂)
  rw [← hc] at h ⊢
  rw [diffQExp_smul_D] at h
  rcases mul_eq_zero.mp h with h | h
  · have hc0 : c = 0 := by exact_mod_cast h
    rw [hc0, zero_smul]
  · exact absurd ((diffQExp_D F x).trans h) hD

end
end S_ModularCurve_diffQExp_qExpFunctionFieldC_injective
end P2MW
export P2MW.S_ModularCurve_diffQExp_qExpFunctionFieldC_injective (solution)
