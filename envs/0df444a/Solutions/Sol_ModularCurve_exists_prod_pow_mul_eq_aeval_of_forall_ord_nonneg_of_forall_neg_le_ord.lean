-- Prove2me | solution 1 for ModularCurve.exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ef40ee8b-5184-52c9-b9cf-d7fa8cbc39c3

import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "charLGeomPlaceEquiv charLGeomPlaceOfPoint jqModC modularFunctionFieldC jqModC_mem exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceEquiv_placeInfty_eq_order order_jqModC"
namespace JLinePoles
p2m_open "ModularCurve"

theorem ord_finset_prod {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ord_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (f : F) :
    v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  have h1 : v.ord (-1 : F) = 0 := by
    have h := v.ord_mul (neg_ne_zero.mpr (one_ne_zero' F)) (neg_ne_zero.mpr (one_ne_zero' F))
    rw [neg_one_mul, neg_neg, v.ord_one] at h
    omega
  rw [← neg_one_mul, v.ord_mul (neg_ne_zero.mpr (one_ne_zero' F)) hf, h1, zero_add]

variable (k : Type*) [Field k]

theorem jt_sub_ne_zero [DecidableEq k] (c : k) : (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k c c
  rw [h, Place.ord_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem ord_placeInfty_jt_sub [DecidableEq k] [DecidableEq (RatFunc k)] (c : k) :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) c) = -1 := by
  have hj : (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) = -1 := by
    rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order]; exact order_jqModC k
  have hj0 : (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hj; exact absurd hj (by norm_num)
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, sub_zero, hj]
  · rw [sub_eq_add_neg, Place.ord_add_eq_of_lt _ hj0 (neg_ne_zero.mpr ((map_ne_zero _).mpr hc)), hj]
    rw [hj, ord_neg, Place.ord_algebraMap]; norm_num

end ModularCurve.JLinePoles

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve.JLinePoles in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] [DecidableEq (RatFunc k)]
    (S₀ : Finset k) (m : k → ℕ) (n : ℕ) (φ : ↥(modularFunctionFieldC k 1))
    (hreg : ∀ b : k, b ∉ S₀ → 0 ≤ (charLGeomPlaceOfPoint k b).ord φ)
    (hS₀ : ∀ a ∈ S₀, -(m a : ℤ) ≤ (charLGeomPlaceOfPoint k a).ord φ)
    (hinf : -(n : ℤ) ≤ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord φ) :
    ∃ Q : Polynomial k, (Q ≠ 0 → Q.natDegree ≤ n + ∑ a ∈ S₀, m a) ∧
      (∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ m a) * φ
        = Polynomial.aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Q := by
  classical
  set ss := ∏ a ∈ S₀, ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ m a with hss_def
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, fun h => (h rfl).elim, by rw [mul_zero, map_zero]⟩
  have hss : ss ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (jt_sub_ne_zero k a)

  have hclass : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) → ∃ b, v = charLGeomPlaceOfPoint k b := by
    intro v hv
    rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k ((charLGeomPlaceEquiv k).symm v)
      with ⟨b, hb⟩ | h
    · exact ⟨b, ((charLGeomPlaceEquiv k).apply_symm_apply v).symm.trans (congrArg (charLGeomPlaceEquiv k) hb)⟩
    · exact absurd (((charLGeomPlaceEquiv k).apply_symm_apply v).symm.trans (congrArg (charLGeomPlaceEquiv k) h)) hv

  have hss_b : ∀ b : k, (charLGeomPlaceOfPoint k b).ord ss = if b ∈ S₀ then (m b : ℤ) else 0 := by
    intro b
    rw [hss_def, ord_finset_prod _ _ _ (fun a _ => pow_ne_zero _ (jt_sub_ne_zero k a))]
    simp_rw [← zpow_natCast, Place.ord_zpow, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq']
  have hss_inf : (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord ss = -((∑ a ∈ S₀, m a : ℕ) : ℤ) := by
    rw [hss_def, ord_finset_prod _ _ _ (fun a _ => pow_ne_zero _ (jt_sub_ne_zero k a))]
    simp_rw [← zpow_natCast, Place.ord_zpow, ord_placeInfty_jt_sub]
    simp [mul_neg, Finset.sum_neg_distrib]

  have hreg' : ∀ v : Place k ↥(modularFunctionFieldC k 1),
      v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) → 0 ≤ v.ord (ss * φ) := by
    intro v hv
    obtain ⟨b, rfl⟩ := hclass v hv
    rw [(charLGeomPlaceOfPoint k b).ord_mul hss hφ, hss_b]
    by_cases hb : b ∈ S₀
    · rw [if_pos hb]; have := hS₀ b hb; omega
    · rw [if_neg hb]; have := hreg b hb; omega
  have hinf' : -((n + ∑ a ∈ S₀, m a : ℕ) : ℤ)
      ≤ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord (ss * φ) := by
    rw [(charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord_mul hss hφ, hss_inf]
    push_cast; omega

  obtain ⟨Q, hQdeg, hQ⟩ :=
    exists_eq_algebraMap_add_prod_mul_aeval_of_forall_ord_nonneg_of_hasValue (∅ : Finset k) (0 : k) (n + ∑ a ∈ S₀, m a)
      (ss * φ) hreg' hinf' (fun a ha => (Finset.notMem_empty a ha).elim)
  refine ⟨Q, fun h => by simpa using hQdeg h, ?_⟩
  rw [hQ, map_zero, zero_add, Finset.prod_empty, one_mul]

end S_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord
end P2MW
export P2MW.S_ModularCurve_exists_prod_pow_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_le_ord (solution)
