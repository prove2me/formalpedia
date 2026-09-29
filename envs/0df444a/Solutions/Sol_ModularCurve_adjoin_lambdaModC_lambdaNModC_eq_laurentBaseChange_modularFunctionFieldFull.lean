-- Prove2me | solution 1 for ModularCurve.adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3a85b057-71ee-5e55-b2a0-7430d53ed239

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve IntermediateField Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_single qExpand_one_apply qExpand_qExpand jq modularFunctionFieldFull jqd_mem_full coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange lambdaModC lambdaNModC laurentMap_coeff laurentBaseChange_adjoin coeffMap_qExpand adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four"
namespace FF4
p2m_open "ModularCurve~coeffEmb_qExpand"

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem coeffEmb_lambdaModC : coeffEmb L (lambdaModC ℚ) = lambdaModC L := by
  ext k
  simp only [coeffEmb, coeffMap_coeff, lambdaModC, laurentMap_coeff]
  simp

abbrev K : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))

abbrev J : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L))

abbrev E : IntermediateField L (LaurentSeries L) := laurentBaseChange L (modularFunctionFieldFull 4)

theorem mu_mem_K : lambdaModC L ∈ K L := IntermediateField.mem_adjoin_simple_self L _

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := coeffMap_qExpand _ n x

theorem J_le_E : J L ≤ E L := by
  rw [J, IntermediateField.adjoin_simple_le_iff]
  have h := coeffEmb_mem_laurentBaseChange L (jqd_mem_full 4 (one_dvd 4))
  rwa [qExpand_one_apply] at h

theorem adjoin_lambdaModC_eq : IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull 4) :=
  ModularCurve.adjoin_lambdaModC_eq_laurentBaseChange_modularFunctionFieldFull_four L

theorem E_le_K : E L ≤ K L := (adjoin_lambdaModC_eq L).symm.le

def qExpandAlg (N : ℕ) [NeZero N] : LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L N with
    commutes' := fun c => by
      show qExpand L N (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) c
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[scoped simp] theorem qExpandAlg_apply (N : ℕ) [NeZero N] (x : LaurentSeries L) : qExpandAlg L N x = qExpand L N x := rfl

variable (q : ℕ) [Fact q.Prime]

abbrev K2 : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L ({lambdaModC L, lambdaNModC L q} : Set (LaurentSeries L))

abbrev E2 : IntermediateField L (LaurentSeries L) := laurentBaseChange L (modularFunctionFieldFull (4 * q))

theorem K_le_K2 : K L ≤ K2 L q := IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

theorem map_K (N : ℕ) [NeZero N] : (K L).map (qExpandAlg L N) =
    IntermediateField.adjoin L ({lambdaNModC L N} : Set (LaurentSeries L)) := by
  rw [IntermediateField.adjoin_map]
  congr 1
  rw [Set.image_singleton]
  rfl

theorem qExpand_mem_adjoin_lambdaN {x : LaurentSeries L} (hx : x ∈ K L) (N : ℕ) [NeZero N] :
    qExpand L N x ∈ IntermediateField.adjoin L ({lambdaNModC L N} : Set (LaurentSeries L)) := by
  rw [← map_K]
  exact ⟨x, hx, rfl⟩

theorem dvd_four_mul_prime' {d : ℕ} (hd : d ∣ 4 * q) : d ∣ 4 ∨ ∃ d', d' ∣ 4 ∧ d = q * d' := by
  have hq := (Fact.out : q.Prime)
  by_cases hqd : q ∣ d
  · obtain ⟨d', rfl⟩ := hqd
    right
    refine ⟨d', ?_, rfl⟩
    have : q * d' ∣ q * 4 := by rwa [mul_comm q 4]
    exact Nat.dvd_of_mul_dvd_mul_left hq.pos this
  · left
    have hcop : Nat.Coprime d q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd |>.symm
    exact hcop.dvd_of_dvd_mul_right hd

theorem E2_le_K2 : E2 L q ≤ K2 L q := by
  rw [E2, modularFunctionFieldFull, laurentBaseChange_adjoin, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨d, hd, hdvd, rfl⟩, rfl⟩
  rcases dvd_four_mul_prime' q hdvd with h4 | ⟨d', hd', rfl⟩
  ·
    exact K_le_K2 L q (E_le_K L (coeffEmb_mem_laurentBaseChange L (jqd_mem_full 4 h4)))
  ·
    haveI : NeZero d' := ⟨fun h => by simp [h] at hd⟩
    have hx : coeffEmb L (qExpand ℚ d' jq) ∈ K L := E_le_K L (coeffEmb_mem_laurentBaseChange L (jqd_mem_full 4 hd'))
    have h2 := qExpand_mem_adjoin_lambdaN L hx q
    rw [← coeffEmb_qExpand, qExpand_qExpand] at h2
    have hle : IntermediateField.adjoin L ({lambdaNModC L q} : Set (LaurentSeries L)) ≤ K2 L q :=
      IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
    exact hle h2

theorem K2_le_E2 : K2 L q ≤ E2 L q := by
  rw [K2, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
  have h4 : (4 : ℕ) ∣ 4 * q := dvd_mul_right 4 q
  have hEE : E L ≤ E2 L q := by
    rw [E, E2, modularFunctionFieldFull, modularFunctionFieldFull, laurentBaseChange_adjoin, laurentBaseChange_adjoin]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨d, hd, hdvd, rfl⟩, rfl⟩
    exact ⟨_, ⟨d, hd, hdvd.trans h4, rfl⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · exact hEE ((adjoin_lambdaModC_eq L).le (mu_mem_K L))
  ·
    have hmap : (E L).map (qExpandAlg L q) ≤ E2 L q := by
      rw [E, modularFunctionFieldFull, laurentBaseChange_adjoin, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
      rintro _ ⟨_, ⟨x, ⟨d, hd, hdvd, rfl⟩, rfl⟩, rfl⟩
      haveI := hd
      rw [qExpandAlg_apply, ← coeffEmb_qExpand, qExpand_qExpand]
      exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full (4 * q) (by rw [mul_comm 4 q]; exact Nat.mul_dvd_mul_left q hdvd))
    apply hmap
    exact ⟨lambdaModC L, (adjoin_lambdaModC_eq L).le (mu_mem_K L), rfl⟩

theorem adjoin_lambdaModC_lambdaNModC_eq :
    IntermediateField.adjoin L ({lambdaModC L, lambdaNModC L q} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull (4 * q)) :=
  le_antisymm (K2_le_E2 L q) (E2_le_K2 L q)

end ModularCurve.FF4
p2m_reactivate "P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve.FF4"
p2m_reactivate "P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve.FF4"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.ModularCurve in
theorem solution (L : Type*) [Field L] [Algebra ℚ L] (q : ℕ) [Fact q.Prime] :
    IntermediateField.adjoin L ({lambdaModC L, lambdaNModC L q} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull (4 * q)) :=
  ModularCurve.FF4.adjoin_lambdaModC_lambdaNModC_eq L q

end S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
end P2MW
export P2MW.S_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull (solution)
