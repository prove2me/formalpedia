-- Prove2me | solution 1 for ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/cc3584b4-f3e7-55c8-8f64-8182baf57688

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coe_mem_fieldBar_of_mem
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_qExpand_linearIndependent_pow
import Theorems.Thm_ModularCurve_FullLevel_laurentBaseChange_gamma0_le_fieldBar
import Theorems.Thm_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq
import Theorems.Thm_ModularCurve_qExpand_mem_qExpFunctionFieldC_of_charP
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_fieldBar_integers_eq
import Theorems.Thm_ModularCurve_FullLevel_exists_jInvariant_mem_integers
import Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero
import Theorems.Thm_ModularCurve_FullLevel_residue_mem_qExpFunctionFieldC_gamma0_and_surj
import Theorems.Thm_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
import Theorems.Thm_ModularCurve_FullLevel_exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff"
p2m_attr_erase "simp" "ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH qExpFunctionFieldC qExpand qExpand_C coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single laurentBaseChange FullLevel.qExpand_coe_mem_fieldBar_of_mem FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand qExpand_linearIndependent_pow FullLevel.laurentBaseChange_gamma0_le_fieldBar FullLevel.dvd_of_redQ_smul_lineInfty_eq qExpand_mem_qExpFunctionFieldC_of_charP FullLevel.exists_regularProlongation_fieldBar_integers_eq FullLevel.exists_jInvariant_mem_integers FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero FullLevel.residue_mem_qExpFunctionFieldC_gamma0_and_surj FullLevel.exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty levelH fieldBar Idx levelAutBar redQ qExpand_coe_mem_fieldBar_of_mem levelAutBar_apply_eq_self_of_coe_eq_qExpand laurentBaseChange_gamma0_le_fieldBar dvd_of_redQ_smul_lineInfty_eq exists_regularProlongation_fieldBar_integers_eq exists_jInvariant_mem_integers relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero residue_mem_qExpFunctionFieldC_gamma0_and_surj exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand"
namespace BorelGauss
namespace ValCount
p2m_open "ModularCurve.FullLevel ModularCurve"

variable {L : Type*} [Field L]

section Master

variable {ι : Type*} [Fintype ι] (V : ι → ValuationSubring L)

private noncomputable def expo (x : L) : ℕ := by
  classical
  exact ∏ i, (if h : x ∈ V i then
    (if IsOfFinOrder (IsLocalRing.residue (V i) ⟨x, h⟩) then orderOf (IsLocalRing.residue (V i) ⟨x, h⟩) else 1)
    else 1)

private theorem expo_pos (x : L) : 0 < expo V x := by
  classical
  unfold expo
  refine Finset.prod_pos fun i _ => ?_
  split_ifs with h hfin
  · exact hfin.orderOf_pos
  · exact Nat.one_pos
  · exact Nat.one_pos

private theorem residue_pow_expo_eq_one {x : L} {i : ι} (h : x ∈ V i)
    (hfin : IsOfFinOrder (IsLocalRing.residue (V i) ⟨x, h⟩)) :
    IsLocalRing.residue (V i) ⟨x, h⟩ ^ expo V x = 1 := by
  classical
  rw [← orderOf_dvd_iff_pow_eq_one]
  unfold expo
  refine (dvd_of_eq ?_).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  rw [dif_pos h, if_pos hfin]

private theorem pow_six_eq_one_of_trinomial {F : Type*} [CommRing F] {t : F} (ht : 1 - t + t ^ 2 = 0) :
    t ^ 6 = 1 := by
  have h3 : t ^ 3 + 1 = 0 := by
    have : (t + 1) * (1 - t + t ^ 2) = t ^ 3 + 1 := by ring
    rw [← this, ht, mul_zero]
  have h3' : t ^ 3 = -1 := by linear_combination h3
  calc t ^ 6 = (t ^ 3) ^ 2 := by ring
    _ = 1 := by rw [h3']; ring

private theorem isUnit_trinomial {x : L} {i : ι} (h : x ∈ V i) :
    IsUnit (⟨1 - x ^ expo V x + x ^ (2 * expo V x),
      add_mem (sub_mem (one_mem _) (pow_mem h _)) (pow_mem h _)⟩ : V i) := by
  classical
  set N := expo V x with hN
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro h0
  set r : IsLocalRing.ResidueField (V i) := IsLocalRing.residue (V i) ⟨x, h⟩ with hr
  have hres : IsLocalRing.residue (V i) ⟨1 - x ^ N + x ^ (2 * N),
      add_mem (sub_mem (one_mem _) (pow_mem h _)) (pow_mem h _)⟩ = 1 - r ^ N + (r ^ N) ^ 2 := by
    have : (⟨1 - x ^ N + x ^ (2 * N), add_mem (sub_mem (one_mem _) (pow_mem h _)) (pow_mem h _)⟩ : V i)
        = 1 - (⟨x, h⟩ : V i) ^ N + ((⟨x, h⟩ : V i) ^ N) ^ 2 := by
      apply Subtype.ext
      simp [← pow_mul, mul_comm 2 N]
    rw [this, map_add, map_sub, map_one, map_pow, map_pow, map_pow]
  rw [hres] at h0
  have h6 : r ^ (6 * N) = 1 := by
    rw [mul_comm, pow_mul]; exact pow_six_eq_one_of_trinomial h0
  have hfin : IsOfFinOrder r :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6 * N, Nat.mul_pos (by norm_num) (expo_pos V x), h6⟩
  have h1 : r ^ N = 1 := residue_pow_expo_eq_one V h hfin
  rw [h1] at h0
  norm_num at h0

private theorem exists_pow_valuation_trinomial (x : L) :
    ∃ N : ℕ, 0 < N ∧ ∀ i,
      (x ∈ V i → (V i).valuation (1 - x ^ N + x ^ (2 * N)) = 1) ∧
      (x ∉ V i → (V i).valuation (1 - x ^ N + x ^ (2 * N)) = (V i).valuation x ^ (2 * N)) := by
  classical
  refine ⟨expo V x, expo_pos V x, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact ((V i).valuation_eq_one_iff _).mp (isUnit_trinomial V h)
  · set N := expo V x
    have hx1 : 1 < (V i).valuation x := by
      rw [← not_le]; exact fun hle => h (((V i).valuation_le_one_iff x).mp hle)
    have hN : 0 < N := expo_pos V x
    have hlt : (V i).valuation (1 - x ^ N) < (V i).valuation (x ^ (2 * N)) := by
      rw [Valuation.map_pow]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) ?_
      rw [Valuation.map_one, Valuation.map_pow, max_lt_iff]
      exact ⟨one_lt_pow₀ hx1 (by omega), pow_lt_pow_right₀ hx1 (by omega)⟩
    rw [Valuation.map_add_eq_of_lt_right _ hlt, Valuation.map_pow]

private theorem exists_mul_mem_forall (x : L) :
    ∃ s : L, (∀ i, s ∈ V i) ∧ (∀ i, x ∈ V i → (V i).valuation s = 1) ∧ (∀ i, s * x ∈ V i) := by
  classical
  obtain ⟨N, hN, hg⟩ := exists_pow_valuation_trinomial V x
  set g := 1 - x ^ N + x ^ (2 * N) with hgdef
  refine ⟨g⁻¹, fun i => ?_, fun i h => ?_, fun i => ?_⟩
  · by_cases h : x ∈ V i
    · rw [← (V i).valuation_le_one_iff, map_inv₀, (hg i).1 h, inv_one]
    · have hx1 : 1 < (V i).valuation x := by
        rw [← not_le]; exact fun hle => h (((V i).valuation_le_one_iff x).mp hle)
      rw [← (V i).valuation_le_one_iff, map_inv₀, (hg i).2 h]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1.le)
  · rw [map_inv₀, (hg i).1 h, inv_one]
  · by_cases h : x ∈ V i
    · rw [← (V i).valuation_le_one_iff, Valuation.map_mul, map_inv₀, (hg i).1 h, inv_one, one_mul]
      exact ((V i).valuation_le_one_iff x).mpr h
    · have hx1 : 1 < (V i).valuation x := by
        rw [← not_le]; exact fun hle => h (((V i).valuation_le_one_iff x).mp hle)
      have hx0 : (V i).valuation x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
      rw [← (V i).valuation_le_one_iff, Valuation.map_mul, map_inv₀, (hg i).2 h]

      have : ((V i).valuation x ^ (2 * N))⁻¹ * (V i).valuation x = ((V i).valuation x ^ (2 * N - 1))⁻¹ := by
        obtain ⟨M, hM⟩ : ∃ M, 2 * N = M + 1 := ⟨2 * N - 1, by omega⟩
        rw [hM, Nat.add_sub_cancel, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hx0, mul_one]
      rw [this]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1.le)

private theorem exists_separator_of {x : L} {i j : ι} (hxi : (V i).valuation x = 1) (hxj : x ∉ V j) :
    ∃ t : L, (∀ l, t ∈ V l) ∧ (V i).valuation t = 1 ∧ (V j).valuation t < 1 := by
  classical
  obtain ⟨N, hN, hg⟩ := exists_pow_valuation_trinomial V x
  set g := 1 - x ^ N + x ^ (2 * N) with hgdef
  have hxiMem : x ∈ V i := ((V i).valuation_le_one_iff x).mp hxi.le
  refine ⟨x ^ N * g⁻¹, fun l => ?_, ?_, ?_⟩
  · by_cases h : x ∈ V l
    · rw [← (V l).valuation_le_one_iff, Valuation.map_mul, map_inv₀, (hg l).1 h, inv_one, mul_one,
        Valuation.map_pow]
      exact pow_le_one₀ zero_le' (((V l).valuation_le_one_iff x).mpr h)
    · have hx1 : 1 < (V l).valuation x := by
        rw [← not_le]; exact fun hle => h (((V l).valuation_le_one_iff x).mp hle)
      have hx0 : (V l).valuation x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
      rw [← (V l).valuation_le_one_iff, Valuation.map_mul, map_inv₀, (hg l).2 h, Valuation.map_pow]
      have : (V l).valuation x ^ N * ((V l).valuation x ^ (2 * N))⁻¹ = ((V l).valuation x ^ N)⁻¹ := by
        rw [two_mul, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx0), one_mul]
      rw [this]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1.le)
  · rw [Valuation.map_mul, map_inv₀, (hg i).1 hxiMem, inv_one, mul_one, Valuation.map_pow, hxi, one_pow]
  · have hx1 : 1 < (V j).valuation x := by
      rw [← not_le]; exact fun hle => hxj (((V j).valuation_le_one_iff x).mp hle)
    have hx0 : (V j).valuation x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
    rw [Valuation.map_mul, map_inv₀, (hg j).2 hxj, Valuation.map_pow]
    have : (V j).valuation x ^ N * ((V j).valuation x ^ (2 * N))⁻¹ = ((V j).valuation x ^ N)⁻¹ := by
      rw [two_mul, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx0), one_mul]
    rw [this]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx1 (by omega))

private theorem exists_separator (hinc : ∀ i j, V i ≤ V j → i = j) (i : ι) :
    ∃ e : L, (∀ l, e ∈ V l) ∧ (V i).valuation e = 1 ∧ ∀ j, j ≠ i → (V j).valuation e < 1 := by
  classical

  have hsep : ∀ j, j ≠ i → ∃ t : L, (∀ l, t ∈ V l) ∧ (V i).valuation t = 1 ∧ (V j).valuation t < 1 := by
    intro j hj
    have hnot : ¬ V i ≤ V j := fun hle => hj (hinc i j hle).symm
    obtain ⟨x, hxi, hxj⟩ := Set.not_subset.mp hnot

    by_cases hu : (V i).valuation x = 1
    · exact exists_separator_of V hu hxj
    · have hlt : (V i).valuation x < 1 := lt_of_le_of_ne (((V i).valuation_le_one_iff x).mpr hxi) hu
      have hu' : (V i).valuation (1 + x) = 1 := by
        rw [Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_one]), Valuation.map_one]
      have hxj' : 1 + x ∉ V j := fun hmem => hxj (by simpa using sub_mem hmem (one_mem (V j)))
      exact exists_separator_of V hu' hxj'
  choose! t ht using hsep
  refine ⟨∏ j ∈ Finset.univ.erase i, t j, fun l => ?_, ?_, fun j hj => ?_⟩
  · exact prod_mem fun j hj => (ht j (Finset.ne_of_mem_erase hj)).1 l
  · rw [map_prod]
    exact Finset.prod_eq_one fun j hj => (ht j (Finset.ne_of_mem_erase hj)).2.1
  · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
    have hle : ∏ l ∈ (Finset.univ.erase i).erase j, (V j).valuation (t l) ≤ 1 :=
      Finset.prod_le_one' fun l hl =>
        ((V j).valuation_le_one_iff _).mpr ((ht l (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl))).1 j)
    exact mul_lt_one_of_lt_of_le (ht j hj).2.2 hle

end Master

section Torsion

variable {K : Type*} [Field K] [Algebra K L]

private theorem exists_ne_map_eq_of_sum_eq_zero {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
    {α : Type*} (s : Finset α) (F : α → L) (hs : ∑ a ∈ s, F a = 0) {a₀ : α} (ha₀ : a₀ ∈ s) (h0 : F a₀ ≠ 0) :
    ∃ a₁ ∈ s, ∃ a₂ ∈ s, a₁ ≠ a₂ ∧ v (F a₁) = v (F a₂) := by
  classical
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image s (fun a => v (F a)) ⟨a₀, ha₀⟩
  by_contra hne
  push Not at hne
  have hlt : ∀ a ∈ s.erase m, v (F a) < v (F m) := fun a ha =>
    lt_of_le_of_ne (hmax a (Finset.mem_of_mem_erase ha)) (hne a (Finset.mem_of_mem_erase ha) m hm
      (Finset.ne_of_mem_erase ha))
  have hm0 : v (F m) ≠ 0 := by
    intro h
    have := hmax a₀ ha₀
    rw [h, le_zero_iff, Valuation.zero_iff] at this
    exact h0 this
  have hsum : v (∑ a ∈ s.erase m, F a) < v (F m) := Valuation.map_sum_lt v hm0 hlt
  have : v (∑ a ∈ s, F a) = v (F m) := by
    rw [← Finset.add_sum_erase s F hm, Valuation.map_add_eq_of_lt_left v hsum]
  rw [hs, Valuation.map_zero] at this
  exact hm0 this.symm

private theorem exists_pow_valuation_eq_algebraMap {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) {y : L} (hy : IsAlgebraic K y) (hy0 : y ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : K, a ≠ 0 ∧ v y ^ n = v (algebraMap K L a) := by
  classical
  obtain ⟨p, hp0, hp⟩ := hy
  have hsum : ∑ m ∈ p.support, algebraMap K L (p.coeff m) * y ^ m = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp
    exact hp
  obtain ⟨m₀, hm₀⟩ : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  have hterm : ∀ m ∈ p.support, algebraMap K L (p.coeff m) * y ^ m ≠ 0 := fun m hm =>
    mul_ne_zero ((map_ne_zero _).mpr (Polynomial.mem_support_iff.mp hm)) (pow_ne_zero _ hy0)
  obtain ⟨m₁, hm₁, m₂, hm₂, hne, heq⟩ :=
    exists_ne_map_eq_of_sum_eq_zero v p.support _ hsum hm₀ (hterm m₀ hm₀)

  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow] at heq
  have hc₁ : p.coeff m₁ ≠ 0 := Polynomial.mem_support_iff.mp hm₁
  have hc₂ : p.coeff m₂ ≠ 0 := Polynomial.mem_support_iff.mp hm₂
  have hv₁ : v (algebraMap K L (p.coeff m₁)) ≠ 0 := (Valuation.ne_zero_iff v).mpr ((map_ne_zero _).mpr hc₁)
  have hv₂ : v (algebraMap K L (p.coeff m₂)) ≠ 0 := (Valuation.ne_zero_iff v).mpr ((map_ne_zero _).mpr hc₂)
  have hvy : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr hy0
  rcases lt_or_gt_of_ne hne with hlt | hlt
  ·
    refine ⟨m₂ - m₁, Nat.sub_pos_of_lt hlt, p.coeff m₁ / p.coeff m₂, div_ne_zero hc₁ hc₂, ?_⟩
    rw [map_div₀, map_div₀, eq_div_iff hv₂]
    obtain ⟨d, hd⟩ : ∃ d, m₂ = m₁ + d := ⟨m₂ - m₁, by omega⟩
    subst hd
    rw [Nat.add_sub_cancel_left]
    rw [pow_add, ← mul_assoc] at heq

    have := mul_right_cancel₀ (pow_ne_zero m₁ hvy)
      (show v (algebraMap K L (p.coeff m₁)) * v y ^ m₁ =
          (v (algebraMap K L (p.coeff (m₁ + d))) * v y ^ d) * v y ^ m₁ by
            rw [heq]; exact mul_right_comm _ _ _)
    rw [this]; exact mul_comm _ _
  · refine ⟨m₁ - m₂, Nat.sub_pos_of_lt hlt, p.coeff m₂ / p.coeff m₁, div_ne_zero hc₂ hc₁, ?_⟩
    rw [map_div₀, map_div₀, eq_div_iff hv₁]
    obtain ⟨d, hd⟩ : ∃ d, m₁ = m₂ + d := ⟨m₁ - m₂, by omega⟩
    subst hd
    rw [Nat.add_sub_cancel_left]
    rw [pow_add, ← mul_assoc] at heq
    have := mul_right_cancel₀ (pow_ne_zero m₂ hvy)
      (show (v (algebraMap K L (p.coeff (m₂ + d))) * v y ^ d) * v y ^ m₂ =
          v (algebraMap K L (p.coeff m₂)) * v y ^ m₂ by
            rw [← heq]; exact mul_right_comm _ _ _)
    rw [← this]; exact mul_comm _ _

end Torsion

section Count

variable {K : Type*} [Field K] [Algebra K L] (OK : ValuationSubring K)

private theorem mem_iff_of_comap_eq {O : ValuationSubring L} (hO : O.comap (algebraMap K L) = OK) (c : K) :
    algebraMap K L c ∈ O ↔ c ∈ OK := by
  rw [← hO, ValuationSubring.mem_comap]

private theorem valuation_lt_one_iff_of_comap_eq {O : ValuationSubring L} (hO : O.comap (algebraMap K L) = OK) (c : K) :
    O.valuation (algebraMap K L c) < 1 ↔ OK.valuation c < 1 := by
  by_cases hc : c = 0
  · subst hc; simp
  constructor
  · intro h
    rw [← not_le]
    intro hle

    have hinv : c⁻¹ ∈ OK := by
      rw [← OK.valuation_le_one_iff, map_inv₀]; exact inv_le_one_of_one_le₀ hle
    have hinv' : (algebraMap K L c)⁻¹ ∈ O := by
      rw [← map_inv₀]; exact (mem_iff_of_comap_eq OK hO _).mpr hinv
    rw [← O.valuation_le_one_iff, map_inv₀] at hinv'
    have h0 : O.valuation (algebraMap K L c) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hc)
    exact absurd ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp hinv') (not_le.mpr h)
  · intro h
    rw [← not_le]
    intro hle
    have hinv' : (algebraMap K L c)⁻¹ ∈ O := by
      rw [← O.valuation_le_one_iff, map_inv₀]; exact inv_le_one_of_one_le₀ hle
    have hinv : c⁻¹ ∈ OK := by
      rw [← mem_iff_of_comap_eq OK hO, map_inv₀]; exact hinv'
    rw [← OK.valuation_le_one_iff, map_inv₀] at hinv
    have h0 : OK.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
    exact absurd ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp hinv) (not_le.mpr h)

private theorem eq_of_le_of_comap_eq [Algebra.IsAlgebraic K L] {O O' : ValuationSubring L}
    (hO : O.comap (algebraMap K L) = OK) (hO' : O'.comap (algebraMap K L) = OK) (hle : O ≤ O') : O = O' := by
  by_contra hne
  have hlt : ¬ O' ≤ O := fun h => hne (le_antisymm hle h)
  obtain ⟨y, hyO', hyO⟩ := Set.not_subset.mp hlt
  have hy0 : y ≠ 0 := fun h => hyO (h ▸ zero_mem O)
  obtain ⟨n, hn, a, ha0, hva⟩ :=
    exists_pow_valuation_eq_algebraMap O.valuation (Algebra.IsAlgebraic.isAlgebraic (R := K) y) hy0

  have hvy : O.valuation y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  have hva' : O.valuation (algebraMap K L a) ≠ 0 := (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr ha0)
  have hu : algebraMap K L a / y ^ n ∈ O := by
    rw [← O.valuation_le_one_iff, map_div₀, Valuation.map_pow, ← hva, div_self (pow_ne_zero _ hvy)]
  have haO' : algebraMap K L a ∈ O' := by
    have : algebraMap K L a = (algebraMap K L a / y ^ n) * y ^ n := by
      rw [div_mul_cancel₀ _ (pow_ne_zero _ hy0)]
    rw [this]; exact mul_mem (hle hu) (pow_mem hyO' _)
  have haOK : a ∈ OK := (mem_iff_of_comap_eq OK hO' a).mp haO'
  have haO : algebraMap K L a ∈ O := (mem_iff_of_comap_eq OK hO a).mpr haOK
  rw [← O.valuation_le_one_iff, ← hva] at haO

  have : O.valuation y ≤ 1 := by
    rw [← not_lt]; intro h1
    exact absurd haO (not_le.mpr (one_lt_pow₀ h1 (by omega)))
  exact hyO ((O.valuation_le_one_iff y).mp this)

variable {ι : Type*} [Fintype ι] (O : ι → ValuationSubring L)

private theorem exists_common_mul {β : Type*} [Fintype β] (b : β → L) (i : ι) (hb : ∀ k, b k ∈ O i) :
    ∃ s : L, (∀ l, s ∈ O l) ∧ (O i).valuation s = 1 ∧ ∀ k l, s * b k ∈ O l := by
  classical
  have h := fun k => exists_mul_mem_forall O (b k)
  choose s hs using h
  refine ⟨∏ k, s k, fun l => prod_mem fun k _ => (hs k).1 l, ?_, fun k l => ?_⟩
  · rw [map_prod]; exact Finset.prod_eq_one fun k _ => (hs k).2.1 i (hb k)
  · rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ k), mul_comm (s k), mul_assoc]
    exact mul_mem (prod_mem fun k' hk' => (hs k').1 l) ((hs k).2.2 l)

private theorem sum_card_le_finrank [FiniteDimensional K L]
    (hO : ∀ i, (O i).comap (algebraMap K L) = OK) (hinj : Function.Injective O)
    {β : ι → Type*} [∀ i, Fintype (β i)] (b : (i : ι) → β i → L) (hb : ∀ i k, b i k ∈ O i)
    (hli : ∀ i (c : β i → K), (∀ k, c k ∈ OK) →
      (O i).valuation (∑ k, algebraMap K L (c k) * b i k) < 1 → ∀ k, OK.valuation (c k) < 1) :
    ∑ i, Fintype.card (β i) ≤ Module.finrank K L := by
  classical

  have hinc : ∀ i j, O i ≤ O j → i = j := fun i j hle =>
    hinj (eq_of_le_of_comap_eq OK (hO i) (hO j) hle)

  choose e he using exists_separator O hinc
  choose s hs using fun i => exists_common_mul O (b i) i (hb i)

  let B : (Σ i, β i) → L := fun x => e x.1 * s x.1 * b x.1 x.2
  have hBlt : ∀ (x : Σ i, β i) (j : ι), j ≠ x.1 → (O j).valuation (B x) < 1 := by
    intro x j hj
    show (O j).valuation (e x.1 * s x.1 * b x.1 x.2) < 1
    rw [mul_assoc, Valuation.map_mul]
    exact mul_lt_one_of_lt_of_le ((he x.1).2.2 j hj)
      (((O j).valuation_le_one_iff _).mpr ((hs x.1).2.2 x.2 j))
  have hli' : LinearIndependent K B := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨x₁, hx₁⟩ := hne
    obtain ⟨x₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun x => OK.valuation (g x)) ⟨x₁, Finset.mem_univ _⟩
    have hg0 : g x₀ ≠ 0 := by
      intro h0
      have := hmax x₁ (Finset.mem_univ _)
      rw [h0, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at this
      exact hx₁ this

    let c : (Σ i, β i) → K := fun x => g x / g x₀
    have hc : ∀ x, c x ∈ OK := fun x => by
      rw [← OK.valuation_le_one_iff]
      show OK.valuation (g x / g x₀) ≤ 1
      rw [map_div₀]
      exact div_le_one_of_le₀ (hmax x (Finset.mem_univ _)) zero_le'
    have hc0 : c x₀ = 1 := div_self hg0
    have hsum : ∑ x, algebraMap K L (c x) * B x = 0 := by
      have : ∑ x, algebraMap K L (c x) * B x = (algebraMap K L (g x₀))⁻¹ * ∑ x, g x • B x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        show algebraMap K L (g x / g x₀) * B x = _
        rw [Algebra.smul_def, map_div₀, div_eq_inv_mul, mul_assoc]
      rw [this, hg, mul_zero]

    obtain ⟨i₀, k₀⟩ := x₀
    rw [Fintype.sum_sigma, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)] at hsum
    have hrest : (O i₀).valuation
        (∑ i ∈ Finset.univ.erase i₀, ∑ k, algebraMap K L (c ⟨i, k⟩) * B ⟨i, k⟩) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
      refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
      rw [Valuation.map_mul, mul_comm]
      exact mul_lt_one_of_lt_of_le (hBlt ⟨i, k⟩ i₀ (Finset.ne_of_mem_erase hi).symm)
        (((O i₀).valuation_le_one_iff _).mpr ((mem_iff_of_comap_eq OK (hO i₀) _).mpr (hc _)))
    have hfirst : (O i₀).valuation (∑ k, algebraMap K L (c ⟨i₀, k⟩) * B ⟨i₀, k⟩) < 1 := by
      have : ∑ k, algebraMap K L (c ⟨i₀, k⟩) * B ⟨i₀, k⟩ =
          -(∑ i ∈ Finset.univ.erase i₀, ∑ k, algebraMap K L (c ⟨i, k⟩) * B ⟨i, k⟩) :=
        eq_neg_of_add_eq_zero_left hsum
      rw [this, Valuation.map_neg]; exact hrest

    have hunit : (O i₀).valuation (e i₀ * s i₀) = 1 := by
      rw [Valuation.map_mul, (he i₀).2.1, (hs i₀).2.1, one_mul]
    have hfac : ∑ k, algebraMap K L (c ⟨i₀, k⟩) * B ⟨i₀, k⟩ =
        (e i₀ * s i₀) * ∑ k, algebraMap K L (c ⟨i₀, k⟩) * b i₀ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      show algebraMap K L (c ⟨i₀, k⟩) * (e i₀ * s i₀ * b i₀ k) = _
      ring
    rw [hfac, Valuation.map_mul, hunit, one_mul] at hfirst
    have := hli i₀ (fun k => c ⟨i₀, k⟩) (fun k => hc _) hfirst k₀
    rw [hc0, Valuation.map_one] at this
    exact lt_irrefl _ this
  have := hli'.fintype_card_le_finrank
  rwa [Fintype.card_sigma] at this

private theorem sum_le_finrank [FiniteDimensional K L]
    (hO : ∀ i, (O i).comap (algebraMap K L) = OK) (hinj : Function.Injective O)
    (f : ι → ℕ) (b : (i : ι) → Fin (f i) → L) (hb : ∀ i k, b i k ∈ O i)
    (hli : ∀ i (c : Fin (f i) → K), (∀ k, c k ∈ OK) →
      (O i).valuation (∑ k, algebraMap K L (c k) * b i k) < 1 → ∀ k, OK.valuation (c k) < 1) :
    ∑ i, f i ≤ Module.finrank K L := by
  have := sum_card_le_finrank OK O hO hinj b hb hli
  simpa using this

end Count

section Uniq

variable {K : Type*} [Field K] [Algebra K L] (OK : ValuationSubring K)

private theorem valuation_lt_one_iff_inv_not_mem (A : ValuationSubring L) {x : L} (hx : x ≠ 0) :
    A.valuation x < 1 ↔ x⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx)),
    not_le]

private theorem comap_valuation_lt_one_iff {L' : Type*} [Field L'] (A : ValuationSubring L) (f : L' →+* L) (x : L') :
    (A.comap f).valuation x < 1 ↔ A.valuation (f x) < 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [valuation_lt_one_iff_inv_not_mem _ hx, valuation_lt_one_iff_inv_not_mem _ ((map_ne_zero f).mpr hx),
    ValuationSubring.mem_comap, map_inv₀]

private theorem comap_algEquiv_eq_of_two_mul_card_gt [FiniteDimensional K L] (O : ValuationSubring L)
    (hO : O.comap (algebraMap K L) = OK) (τ : L ≃ₐ[K] L)
    {β : Type*} [Fintype β] (b : β → L) (hb : ∀ k, b k ∈ O)
    (hli : ∀ c : β → K, (∀ k, c k ∈ OK) →
      O.valuation (∑ k, algebraMap K L (c k) * b k) < 1 → ∀ k, OK.valuation (c k) < 1)
    (hf : Module.finrank K L < 2 * Fintype.card β) :
    O.comap (τ : L →+* L) = O := by
  classical
  by_contra hne

  let P : Bool → ValuationSubring L := fun t => if t then O else O.comap (τ : L →+* L)
  have hP : ∀ t, (P t).comap (algebraMap K L) = OK := by
    intro t
    cases t
    · show ((O.comap (τ : L →+* L)).comap (algebraMap K L)) = OK
      ext c
      rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ← hO, ValuationSubring.mem_comap]
      show τ (algebraMap K L c) ∈ O ↔ _
      rw [AlgEquiv.commutes]
    · exact hO
  have hinj : Function.Injective P := by
    intro t t' h
    cases t <;> cases t'
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl
  let fam : (t : Bool) → β → L := fun t k => if t then b k else τ.symm (b k)
  have hfam : ∀ t k, fam t k ∈ P t := by
    intro t k
    cases t
    · show τ.symm (b k) ∈ O.comap (τ : L →+* L)
      rw [ValuationSubring.mem_comap]
      show τ (τ.symm (b k)) ∈ O
      rw [AlgEquiv.apply_symm_apply]; exact hb k
    · exact hb k
  have hli' : ∀ t (c : β → K), (∀ k, c k ∈ OK) →
      (P t).valuation (∑ k, algebraMap K L (c k) * fam t k) < 1 → ∀ k, OK.valuation (c k) < 1 := by
    intro t c hc hlt
    cases t
    · refine hli c hc ?_
      have h := (comap_valuation_lt_one_iff O (τ : L →+* L) _).mp hlt
      have : (τ : L →+* L) (∑ k, algebraMap K L (c k) * τ.symm (b k)) = ∑ k, algebraMap K L (c k) * b k := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul]
        show τ (algebraMap K L (c k)) * τ (τ.symm (b k)) = _
        rw [AlgEquiv.commutes, AlgEquiv.apply_symm_apply]
      have hfamf : (fun k => algebraMap K L (c k) * fam false k) = fun k => algebraMap K L (c k) * τ.symm (b k) :=
        rfl
      rw [hfamf, this] at h
      exact h
    · exact hli c hc hlt
  have := sum_card_le_finrank OK P hP hinj fam hfam hli'
  simp at this
  omega

private theorem comap_algEquiv_eq_of_two_mul_gt [FiniteDimensional K L] (O : ValuationSubring L)
    (hO : O.comap (algebraMap K L) = OK) (τ : L ≃ₐ[K] L)
    (f : ℕ) (b : Fin f → L) (hb : ∀ k, b k ∈ O)
    (hli : ∀ c : Fin f → K, (∀ k, c k ∈ OK) →
      O.valuation (∑ k, algebraMap K L (c k) * b k) < 1 → ∀ k, OK.valuation (c k) < 1)
    (hf : Module.finrank K L < 2 * f) :
    O.comap (τ : L →+* L) = O :=
  comap_algEquiv_eq_of_two_mul_card_gt OK O hO τ b hb hli (by simpa using hf)

end Uniq

section Tower

variable {K : Type*} [Field K] [Algebra K L] (OK : ValuationSubring K) (O : ValuationSubring L)

private theorem liftIndep_mul {α β : Type*} [Fintype α] [Fintype β] (u : α → L) (v : β → L)
    (hv : ∀ c : β → K, (∀ m, c m ∈ OK) →
      O.valuation (∑ m, algebraMap K L (c m) * v m) < 1 → ∀ m, OK.valuation (c m) < 1)
    (hu : ∀ c : α → β → K, (∀ i m, c i m ∈ OK) →
      O.valuation (∑ i, (∑ m, algebraMap K L (c i m) * v m) * u i) < 1 →
        ∀ i, O.valuation (∑ m, algebraMap K L (c i m) * v m) < 1)
    (c : α × β → K) (hc : ∀ x, c x ∈ OK)
    (hlt : O.valuation (∑ x, algebraMap K L (c x) * (u x.1 * v x.2)) < 1) :
    ∀ x, OK.valuation (c x) < 1 := by
  classical
  have hsum : ∑ x : α × β, algebraMap K L (c x) * (u x.1 * v x.2) =
      ∑ i, (∑ m, algebraMap K L (c (i, m)) * v m) * u i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hsum] at hlt
  intro x
  obtain ⟨i, m⟩ := x
  exact hv (fun m => c (i, m)) (fun m => hc _) (hu (fun i m => c (i, m)) (fun i m => hc _) hlt i) m

end Tower

section Chevalley

variable {F F' : Type*} [Field F] [Field F'] (ι : F →+* F')

private theorem exists_comap_eq (O : ValuationSubring F) : ∃ V : ValuationSubring F', V.comap ι = O := by
  classical
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (O.toLocalSubring.map ι)
  refine ⟨V, ?_⟩
  obtain ⟨hsub, hloc⟩ := LocalSubring.le_def.mp hV
  have hmapmem : ∀ x ∈ O, ι x ∈ (O.toLocalSubring.map ι).toSubring := fun x hx => by
    rw [LocalSubring.map_toSubring, Subring.mem_map]
    exact ⟨x, show x ∈ O.toLocalSubring.toSubring from hx, rfl⟩
  have h1 : O ≤ V.comap ι := fun x hx => ValuationSubring.mem_comap.mpr (hsub (hmapmem x hx))
  refine le_antisymm ?_ h1
  intro x hx
  rw [ValuationSubring.mem_comap] at hx
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ zero_mem O)

  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  let a : (O.toLocalSubring.map ι).toSubring := ⟨ι x⁻¹, hmapmem _ hinv⟩
  have hnu : ¬ IsUnit a := by
    rintro ⟨u, hu⟩

    have hmem : (((u⁻¹ : (O.toLocalSubring.map ι).toSubringˣ) : (O.toLocalSubring.map ι).toSubring) : F') ∈
        (LocalSubring.map ι O.toLocalSubring).toSubring := (u⁻¹ : (O.toLocalSubring.map ι).toSubringˣ).1.2
    have hmem' : (((u⁻¹ : (O.toLocalSubring.map ι).toSubringˣ) : (O.toLocalSubring.map ι).toSubring) : F') ∈
        Subring.map ι O.toLocalSubring.toSubring := by
      rw [← LocalSubring.map_toSubring]; exact hmem
    obtain ⟨y, hyO, hy⟩ := Subring.mem_map.mp hmem'
    have hprod : (a : F') * ((u⁻¹ : (O.toLocalSubring.map ι).toSubringˣ) : (O.toLocalSubring.map ι).toSubring) = 1 := by
      rw [← hu, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hprod' : ι (x⁻¹ * y) = 1 := by
      rw [map_mul, hy]; exact hprod
    have hxy : x⁻¹ * y = 1 := ι.injective (by rw [hprod', map_one])
    have : y = x := by
      have := congrArg (x * ·) hxy
      simpa [← mul_assoc, mul_inv_cancel₀ hx0] using this
    exact hxO (this ▸ (show y ∈ O from hyO))

  have hnuV : ¬ IsUnit (Subring.inclusion hsub a) := fun h => hnu (hloc.map_nonunit a h)

  apply hnuV
  refine isUnit_iff_exists_inv.mpr ⟨⟨ι x, hx⟩, ?_⟩
  apply Subtype.ext
  show ι x⁻¹ * ι x = 1
  rw [← map_mul, inv_mul_cancel₀ hx0, map_one]

private theorem comap_eq_of_unique {K : Type*} [Field K] (κF : K →+* F) (ι : F →+* F')
    (Osharp : ValuationSubring F')
    (huniq : ∀ V : ValuationSubring F', V.comap (ι.comp κF) = Osharp.comap (ι.comp κF) → V = Osharp)
    (O' : ValuationSubring F) (hO' : O'.comap κF = Osharp.comap (ι.comp κF)) :
    O' = Osharp.comap ι := by
  obtain ⟨V, hV⟩ := exists_comap_eq ι O'
  have : V = Osharp := huniq V (by rw [← ValuationSubring.comap_comap, hV, hO'])
  rw [← hV, this]

end Chevalley

section UniqByCount

variable {K : Type*} [Field K] [Algebra K L] (OK : ValuationSubring K)

private theorem eq_of_comap_eq_of_finrank_le_card [FiniteDimensional K L] (O : ValuationSubring L)
    (hO : O.comap (algebraMap K L) = OK)
    {β : Type*} [Fintype β] (b : β → L) (hb : ∀ k, b k ∈ O)
    (hli : ∀ c : β → K, (∀ k, c k ∈ OK) →
      O.valuation (∑ k, algebraMap K L (c k) * b k) < 1 → ∀ k, OK.valuation (c k) < 1)
    (hf : Module.finrank K L ≤ Fintype.card β)
    (V : ValuationSubring L) (hV : V.comap (algebraMap K L) = OK) : V = O := by
  classical
  by_contra hne
  let P : Bool → ValuationSubring L := fun t => if t then O else V
  have hP : ∀ t, (P t).comap (algebraMap K L) = OK := by
    intro t; cases t
    · exact hV
    · exact hO
  have hinj : Function.Injective P := by
    intro t t' h
    cases t <;> cases t'
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl
  let f : Bool → ℕ := fun t => match t with
    | true => Fintype.card β
    | false => 1
  let e : β ≃ Fin (f true) := Fintype.equivFin β
  let fam : (t : Bool) → Fin (f t) → L := fun t => match t with
    | true => fun k => b (e.symm k)
    | false => fun _ => 1
  have hfam : ∀ t k, fam t k ∈ P t := by
    intro t k; cases t
    · exact one_mem V
    · exact hb _
  have hli' : ∀ t (c : Fin (f t) → K), (∀ k, c k ∈ OK) →
      (P t).valuation (∑ k, algebraMap K L (c k) * fam t k) < 1 → ∀ k, OK.valuation (c k) < 1 := by
    intro t c hc hlt k
    cases t
    ·
      have hsub : ∀ k' : Fin (f false), k' = k := by
        intro k'
        have h1 : k'.val < 1 := k'.2
        have h2 : k.val < 1 := k.2
        exact Fin.ext (by omega)
      have hsum : ∑ k', algebraMap K L (c k') * fam false k' = algebraMap K L (c k) := by
        rw [Finset.sum_eq_single k (fun k' _ hk' => absurd (hsub k') hk') (fun h => absurd (Finset.mem_univ k) h)]
        show algebraMap K L (c k) * 1 = _
        rw [mul_one]
      have h1 : V.valuation (algebraMap K L (c k)) < 1 := by
        rw [← hsum]; exact hlt
      exact (valuation_lt_one_iff_of_comap_eq OK hV (c k)).mp h1
    ·
      have hsum : ∑ k', algebraMap K L (c k') * fam true k' = ∑ x : β, algebraMap K L (c (e x)) * b x := by
        rw [← Equiv.sum_comp e]
        refine Finset.sum_congr rfl fun x _ => ?_
        show algebraMap K L (c (e x)) * b (e.symm (e x)) = _
        rw [Equiv.symm_apply_apply]
      have hlt' : O.valuation (∑ x : β, algebraMap K L (c (e x)) * b x) < 1 := by
        rw [← hsum]; exact hlt
      have := hli (fun x => c (e x)) (fun x => hc _) hlt' (e.symm k)
      simpa using this
  have hcount := sum_le_finrank OK P hP hinj f fam hfam hli'
  have hsumf : (∑ t : Bool, f t) = Fintype.card β + 1 := by
    rw [Fintype.sum_bool]
  omega

end UniqByCount

end ModularCurve.FullLevel.BorelGauss.ValCount

set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH qExpFunctionFieldC qExpand qExpand_C coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single laurentBaseChange FullLevel.qExpand_coe_mem_fieldBar_of_mem FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand qExpand_linearIndependent_pow FullLevel.laurentBaseChange_gamma0_le_fieldBar FullLevel.dvd_of_redQ_smul_lineInfty_eq qExpand_mem_qExpFunctionFieldC_of_charP FullLevel.exists_regularProlongation_fieldBar_integers_eq FullLevel.exists_jInvariant_mem_integers FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero FullLevel.residue_mem_qExpFunctionFieldC_gamma0_and_surj FullLevel.exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty levelH fieldBar Idx levelAutBar redQ qExpand_coe_mem_fieldBar_of_mem levelAutBar_apply_eq_self_of_coe_eq_qExpand laurentBaseChange_gamma0_le_fieldBar dvd_of_redQ_smul_lineInfty_eq exists_regularProlongation_fieldBar_integers_eq exists_jInvariant_mem_integers relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero residue_mem_qExpFunctionFieldC_gamma0_and_surj exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand"
namespace BorelGauss
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

@[reducible] private def instAlgResFb (A : ValuationSubring (AlgebraicClosure ℚ)) (Γ : Subgroup SL(2, ℤ)) :
    Algebra (ResidueField A) (qExpFunctionFieldC (ResidueField A) Γ) := inferInstance
@[reducible] private def instAlgLF (Γ : Subgroup SL(2, ℤ)) :
    Algebra (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := inferInstance
attribute [local instance] instAlgResFb instAlgLF

private abbrev Kone : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M')))

private abbrev Kzero : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))

private def qExpandBar (N : ℕ) [NeZero N] :
    LaurentSeries (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) where
  __ := qExpand (AlgebraicClosure ℚ) N
  commutes' r := by
    show qExpand (AlgebraicClosure ℚ) N (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) r
    have h1 : algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ)) r = PowerSeries.C r := by
      simp
    rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C, qExpand_C]

@[scoped simp] private theorem qExpandBar_apply (N : ℕ) [NeZero N] (f : LaurentSeries (AlgebraicClosure ℚ)) :
    qExpandBar N f = qExpand (AlgebraicClosure ℚ) N f := rfl

private def KB : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  (Kone q M').map (qExpandBar q)

omit [NeZero M'] in
private theorem mem_KB_iff (x : LaurentSeries (AlgebraicClosure ℚ)) :
    x ∈ KB q M' ↔ ∃ g ∈ Kone q M', qExpand (AlgebraicClosure ℚ) q g = x := by
  simp [KB, IntermediateField.mem_map]

private theorem _root_.ModularCurve.FullLevel.BorelGauss.qExpand_coe_mem_fieldBar_of_mem (hqM' : ¬ q ∣ M')
    (g : LaurentSeries (AlgebraicClosure ℚ)) (hg : g ∈ Kone q M') :
    qExpand (AlgebraicClosure ℚ) q g ∈ fieldBar q M' :=
  ModularCurve.FullLevel.qExpand_coe_mem_fieldBar_of_mem q M' hqM' g hg

p2m_export "ModularCurve.FullLevel.BorelGauss" "qExpand_coe_mem_fieldBar_of_mem"

private theorem _root_.ModularCurve.FullLevel.BorelGauss.levelAutBar_apply_eq_self_of_coe_eq_qExpand (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hc : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (g : LaurentSeries (AlgebraicClosure ℚ)) (hg : g ∈ Kone q M')
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g) :
    levelAutBar q M' ζ δ x = x :=
  ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand q M' hqM' ζ δ hδ hc g hg x hx

p2m_export "ModularCurve.FullLevel.BorelGauss" "levelAutBar_apply_eq_self_of_coe_eq_qExpand"
private theorem KB_le_fieldBar (hqM' : ¬ q ∣ M') : KB q M' ≤ fieldBar q M' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (mem_KB_iff q M' x).mp hx
  exact qExpand_coe_mem_fieldBar_of_mem q M' hqM' g hg

section WithFact

variable [hqM : Fact (¬ q ∣ M')]

scoped instance algebraKB : Algebra (KB q M') (fieldBar q M') :=
  (IntermediateField.inclusion (KB_le_fieldBar q M' hqM.out)).toRingHom.toAlgebra

scoped instance moduleKB : Module (KB q M') (fieldBar q M') := (algebraKB q M').toModule

private theorem coe_algebraMap_KB (x : KB q M') :
    ((algebraMap (KB q M') (fieldBar q M') x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) = x := rfl

private theorem finrank_KB_eq_relfinrank :
    Module.finrank (KB q M') (fieldBar q M') = (KB q M').relfinrank (fieldBar q M') := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (KB_le_fieldBar q M' hqM.out)]
  rfl

omit [NeZero M'] hqM in
private theorem KB_eq_adjoin_image :
    KB q M' = IntermediateField.adjoin (AlgebraicClosure ℚ)
      (qExpand (AlgebraicClosure ℚ) q ''
        (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M'))) :
          Set (LaurentSeries (AlgebraicClosure ℚ)))) := by
  rw [KB]
  conv_lhs => rw [← IntermediateField.adjoin_self (AlgebraicClosure ℚ) (Kone q M')]
  rw [IntermediateField.adjoin_map]
  congr 1

private theorem finiteDimensional_KB : FiniteDimensional (KB q M') (fieldBar q M') := by
  have h := ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero q M' hqM.out
  rw [← KB_eq_adjoin_image, ← finrank_KB_eq_relfinrank] at h
  exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)

private theorem finrank_KB_le_of_eq_two (hq2 : q = 2) : Module.finrank (KB q M') (fieldBar q M') ≤ 2 := by
  rw [finrank_KB_eq_relfinrank, KB_eq_adjoin_image]
  exact ModularCurve.FullLevel.relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_le_of_eq_two q hq2 M' hqM.out

private def tauB (ζ : Idx q) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hc : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    fieldBar q M' ≃ₐ[KB q M'] fieldBar q M' :=
  { (levelAutBar q M' ζ δ : fieldBar q M' ≃+* fieldBar q M') with
    commutes' := fun k => by
      obtain ⟨g, hg, hgk⟩ := (mem_KB_iff q M' (k : LaurentSeries (AlgebraicClosure ℚ))).mp k.2
      show levelAutBar q M' ζ δ (algebraMap (KB q M') (fieldBar q M') k) = algebraMap (KB q M') (fieldBar q M') k
      exact levelAutBar_apply_eq_self_of_coe_eq_qExpand q M' hqM.out ζ δ hδ hc g hg _
        (by rw [coe_algebraMap_KB, hgk]) }

private theorem coe_tauB (ζ : Idx q) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hc : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ((tauB q M' ζ δ hδ hc : fieldBar q M' ≃ₐ[KB q M'] fieldBar q M') : fieldBar q M' →+* fieldBar q M') =
      (levelAutBar q M' ζ δ).toAlgHom.toRingHom := rfl

private theorem comap_levelAutBar_eq_of_family (hq2 : q = 2) (ζ : Idx q) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (hc : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (O : ValuationSubring (fieldBar q M')) {β : Type*} [Fintype β] (b : β → fieldBar q M') (hb : ∀ k, b k ∈ O)
    (hli : ∀ c : β → KB q M', (∀ k, algebraMap (KB q M') (fieldBar q M') (c k) ∈ O) →
      O.valuation (∑ k, algebraMap (KB q M') (fieldBar q M') (c k) * b k) < 1 →
        ∀ k, O.valuation (algebraMap (KB q M') (fieldBar q M') (c k)) < 1)
    (hcard : 2 < 2 * Fintype.card β) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O := by
  haveI := finiteDimensional_KB q M'
  set OK : ValuationSubring (KB q M') := O.comap (algebraMap (KB q M') (fieldBar q M')) with hOK
  have hli' : ∀ c : β → KB q M', (∀ k, c k ∈ OK) →
      O.valuation (∑ k, algebraMap (KB q M') (fieldBar q M') (c k) * b k) < 1 → ∀ k, OK.valuation (c k) < 1 := by
    intro c hcO hlt k
    rw [← ValCount.valuation_lt_one_iff_of_comap_eq OK (O := O) rfl]
    exact hli c (fun k => (ValuationSubring.mem_comap.mp (hcO k))) hlt k
  have h := ValCount.comap_algEquiv_eq_of_two_mul_card_gt OK O rfl (tauB q M' ζ δ hδ hc) b hb hli'
    (lt_of_le_of_lt (finrank_KB_le_of_eq_two q M' hq2) hcard)
  rwa [coe_tauB] at h

end WithFact

section Family

variable [hqM : Fact (¬ q ∣ M')]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem Kzero_le_fieldBar : Kzero M' ≤ fieldBar q M' :=
  ModularCurve.FullLevel.laurentBaseChange_gamma0_le_fieldBar q M'

private theorem exists_regularProlongation_integers_eq
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ R : RegularProlongation A (fieldBar q M')
        (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))),
      R.integers = O ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by
  exact ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq q M' A O hO

variable (R : RegularProlongation A (fieldBar q M')
  (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))

section ResLaw

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (Rg : RegularProlongation A (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
    (qExpFunctionFieldC (ResidueField A) Γ'))

local notation "LL" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
local notation "EE" => qExpFunctionFieldC (ResidueField A) Γ'

private theorem residue_mul_eq_of_fracForm
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ Rg.integers,
          ((Rg.residue ⟨_, hOy⟩ : EE) : LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (f : FF) (hf : f ∈ Rg.integers) (c : LL) (x y : LaurentSeries A)
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0)
    (hxF : coeffMap A.subtype x ∈ FF) (hyF : coeffMap A.subtype y ∈ FF)
    (hfrac : (f : LaurentSeries LL) * coeffMap A.subtype y = algebraMap LL (LaurentSeries LL) c * coeffMap A.subtype x) :
    ∃ hc : c ∈ A, ((Rg.residue ⟨f, hf⟩ : EE) : LaurentSeries (ResidueField A)) * coeffMap (IsLocalRing.residue A) y =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A ⟨c, hc⟩) *
        coeffMap (IsLocalRing.residue A) x := by
  obtain ⟨hxO, hxres⟩ := hpin x hxF
  obtain ⟨hyO, hyres⟩ := hpin y hyF

  have hxunit : IsUnit (⟨⟨coeffMap A.subtype x, hxF⟩, hxO⟩ : Rg.integers) := by
    apply Rg.isUnit_of_residue_ne_zero
    intro h0
    apply hx
    rw [← hxres, h0]; rfl
  obtain ⟨u, hu⟩ := hxunit
  have hcF : (algebraMap LL FF c : LaurentSeries LL) = algebraMap LL (LaurentSeries LL) c := rfl
  have hid : f * ⟨coeffMap A.subtype y, hyF⟩ = algebraMap LL FF c * ⟨coeffMap A.subtype x, hxF⟩ := by
    apply Subtype.ext
    show (f : LaurentSeries LL) * coeffMap A.subtype y = (algebraMap LL FF c : LaurentSeries LL) * coeffMap A.subtype x
    rw [hcF, hfrac]
  have hinv : (⟨coeffMap A.subtype x, hxF⟩ : FF) * (((u⁻¹ : (Rg.integers)ˣ) : Rg.integers) : FF) = 1 := by
    have h2 := congrArg (fun z : Rg.integers => (z : FF)) u.mul_inv
    rw [hu] at h2
    simpa using h2
  have hgO : algebraMap LL FF c ∈ Rg.integers := by
    have h1 : algebraMap LL FF c = f * ⟨coeffMap A.subtype y, hyF⟩ * (((u⁻¹ : (Rg.integers)ˣ) : Rg.integers) : FF) := by
      rw [hid, mul_assoc, hinv, mul_one]
    rw [h1]
    exact Rg.integers.mul_mem _ _ (Rg.integers.mul_mem _ _ hf hyO) ((u⁻¹ : (Rg.integers)ˣ) : Rg.integers).2
  have hc : c ∈ A := (Rg.algebraMap_mem_iff c).mp hgO
  refine ⟨hc, ?_⟩
  have hidO : (⟨f, hf⟩ : Rg.integers) * ⟨⟨coeffMap A.subtype y, hyF⟩, hyO⟩ =
      ⟨algebraMap LL FF ((⟨c, hc⟩ : A) : LL), (Rg.algebraMap_mem_iff _).mpr hc⟩ * ⟨⟨coeffMap A.subtype x, hxF⟩, hxO⟩ :=
    Subtype.ext hid
  have hres := congrArg Rg.residue hidO
  rw [map_mul, map_mul, Rg.residue_algebraMap ⟨c, hc⟩] at hres
  have hres' := congrArg (fun z : EE => (z : LaurentSeries (ResidueField A))) hres
  simp only [MulMemClass.coe_mul] at hres'
  rw [hxres, hyres] at hres'
  rw [hres']
  rfl

private theorem residue_mul_eq_of_presentation (hT : ModularGroup.T ∈ Γ)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ Rg.integers,
          ((Rg.residue ⟨_, hOy⟩ : EE) : LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y)
    (f : FF) (hf : f ∈ Rg.integers) (x y : LaurentSeries A)
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hxy : (f : LaurentSeries LL) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ((Rg.residue ⟨f, hf⟩ : EE) : LaurentSeries (ResidueField A)) * coeffMap (IsLocalRing.residue A) y =
      coeffMap (IsLocalRing.residue A) x := by
  have hinj : Function.Injective (coeffMap A.subtype : LaurentSeries A → LaurentSeries LL) := by
    intro a b h
    apply HahnSeries.ext; funext k
    have := congrArg (fun s : LaurentSeries LL => s.coeff k) h
    simp only [coeffMap_coeff] at this
    exact Subtype.ext this
  by_cases hf0 : f = 0
  · subst hf0
    have hx : x = 0 := hinj (by rw [map_zero, ← hxy, ZeroMemClass.coe_zero, zero_mul])
    have : (⟨(0 : FF), hf⟩ : Rg.integers) = 0 := rfl
    rw [this, map_zero, hx, map_zero, ZeroMemClass.coe_zero, zero_mul]
  obtain ⟨c, x', y', hc0, hx', hy', hx'F, hy'F, hfrac⟩ :=
    ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A Γ hT f hf0
  obtain ⟨hc, hres'⟩ := residue_mul_eq_of_fracForm A Γ Γ' Rg hpin f hf c x' y' hx' hx'F hy'F hfrac

  have hA1 : x * y' = HahnSeries.C (⟨c, hc⟩ : A) * x' * y := by
    apply hinj
    rw [map_mul, map_mul, map_mul, ← hxy, HahnSeries.C_apply, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    calc (f : LaurentSeries LL) * coeffMap A.subtype y * coeffMap A.subtype y'
        = (f : LaurentSeries LL) * coeffMap A.subtype y' * coeffMap A.subtype y := by ring
      _ = algebraMap LL (LaurentSeries LL) c * coeffMap A.subtype x' * coeffMap A.subtype y := by rw [hfrac]
      _ = _ := by rfl
  have hred := congrArg (coeffMap (IsLocalRing.residue A)) hA1
  rw [map_mul, map_mul, map_mul, HahnSeries.C_apply, coeffMap_single, ← algebraMap_laurentSeries_eq_single] at hred
  apply mul_right_cancel₀ hy'
  calc ((Rg.residue ⟨f, hf⟩ : EE) : LaurentSeries (ResidueField A)) * coeffMap (IsLocalRing.residue A) y *
        coeffMap (IsLocalRing.residue A) y'
      = ((Rg.residue ⟨f, hf⟩ : EE) : LaurentSeries (ResidueField A)) * coeffMap (IsLocalRing.residue A) y' *
        coeffMap (IsLocalRing.residue A) y := by ring
    _ = algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A ⟨c, hc⟩) *
        coeffMap (IsLocalRing.residue A) x' * coeffMap (IsLocalRing.residue A) y := by rw [hres']
    _ = coeffMap (IsLocalRing.residue A) x * coeffMap (IsLocalRing.residue A) y' := hred.symm

end ResLaw

private theorem residue_algebraMap_KB_eq_qExpand (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y)
    (k : KB q M') (hk : algebraMap (KB q M') (fieldBar q M') k ∈ R.integers) :
    ∃ e : LaurentSeries (ResidueField A), e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M') ∧
      ((R.residue ⟨_, hk⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
        qExpand (ResidueField A) q e := by
  obtain ⟨g, hg, hgk⟩ := (mem_KB_iff q M' (k : LaurentSeries (AlgebraicClosure ℚ))).mp k.2
  have hres := fun (f : fieldBar q M') (hf : f ∈ R.integers) (x y : LaurentSeries A)
      (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
      (hxy : (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) =>
    residue_mul_eq_of_presentation A (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))
      (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) R (ModularCurve.translation_mem_GammaH _ _) hpin f hf x y hy hxy
  exact ModularCurve.FullLevel.exists_mem_qExpFunctionFieldC_gamma0_and_residue_eq_qExpand_of_coe_eq_qExpand q M'
    hqM.out A hA R hR hres g hg _ ((coe_algebraMap_KB q M' k).trans hgk.symm) hk

private theorem _root_.ModularCurve.FullLevel.BorelGauss.qExpand_linearIndependent_pow (κ : Type*) [Field κ] [CharP κ q]
    (j : LaurentSeries κ) (hj : j.coeff (-1) ≠ 0) (e : Fin q → LaurentSeries κ)
    (h : ∑ m, qExpand κ q (e m) * j ^ (m : ℕ) = 0) : ∀ m, e m = 0 :=
  ModularCurve.qExpand_linearIndependent_pow κ q j hj e h

p2m_export "ModularCurve.FullLevel.BorelGauss" "qExpand_linearIndependent_pow"

private theorem qExpand_mem_qExpFunctionFieldC_of_mem (hA : A.LiesOverPrime q)
    (e : LaurentSeries (ResidueField A)) (he : e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M')) :
    qExpand (ResidueField A) q e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M') := by
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  exact ModularCurve.qExpand_mem_qExpFunctionFieldC_of_charP (ResidueField A) q (Gamma0 M') e he

private theorem exists_j (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    ∃ (j : fieldBar q M') (hj : j ∈ R.integers),
      (j : LaurentSeries (AlgebraicClosure ℚ)) ∈ Kzero M' ∧
      ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)).coeff (-1) ≠ 0 ∧
      ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) ∈
        qExpFunctionFieldC (ResidueField A) (Gamma0 M') :=
  ModularCurve.FullLevel.exists_jInvariant_mem_integers q M' A R hA hR hpin

private theorem residue_mem_E0_and_surj (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    (∀ (f : fieldBar q M') (hf : f ∈ R.integers), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Kzero M' →
      ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) ∈
        qExpFunctionFieldC (ResidueField A) (Gamma0 M')) ∧
    (∀ e ∈ qExpFunctionFieldC (ResidueField A) (Gamma0 M'),
      ∃ (f : fieldBar q M') (hf : f ∈ R.integers), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Kzero M' ∧
        ((R.residue ⟨f, hf⟩ : qExpFunctionFieldC (ResidueField A)
            (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) = e) :=
  ModularCurve.FullLevel.residue_mem_qExpFunctionFieldC_gamma0_and_surj q M' A R hA hR hpin

end Family

section Assembly

variable [hqM : Fact (¬ q ∣ M')]
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable (R : RegularProlongation A (fieldBar q M')
  (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))))

private theorem _root_.ModularCurve.FullLevel.BorelGauss.dvd_of_redQ_smul_lineInfty_eq (δ : SL(2, ℤ)) (hfix : redQ q δ • lineInfty q = lineInfty q) :
    (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
  ModularCurve.FullLevel.dvd_of_redQ_smul_lineInfty_eq q δ hfix

p2m_export "ModularCurve.FullLevel.BorelGauss" "dvd_of_redQ_smul_lineInfty_eq"

private theorem valuation_lt_one_iff_residue_eq_zero (z : R.integers) :
    R.integers.valuation (z : fieldBar q M') < 1 ↔ R.residue z = 0 := by
  rw [← ValuationSubring.valuation_lt_one_iff, ← R.ker_residue, RingHom.mem_ker]

private theorem coe_sum_mul_pow {n : ℕ} (x : Fin n → R.integers) (y : R.integers) :
    ((∑ m, x m * y ^ (m : ℕ) : R.integers) : fieldBar q M') = ∑ m, (x m : fieldBar q M') * (y : fieldBar q M') ^ (m : ℕ) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]

private theorem residue_sub_eq_zero_iff (x y : R.integers) : R.residue (x - y) = 0 ↔ R.residue x = R.residue y := by
  rw [map_sub, sub_eq_zero]

private theorem residue_sum_mul_pow {n : ℕ} (x : Fin n → R.integers) (y : R.integers) :
    R.residue (∑ m, x m * y ^ (m : ℕ)) = ∑ m, R.residue (x m) * R.residue y ^ (m : ℕ) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_pow]

private theorem coe_residue_sum_mul_pow {n : ℕ}
    (x : Fin n → qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')))
    (y : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
    ((∑ m, x m * y ^ (m : ℕ) : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
      LaurentSeries (ResidueField A)) =
      ∑ m, (x m : LaurentSeries (ResidueField A)) * (y : LaurentSeries (ResidueField A)) ^ (m : ℕ) := by
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]

private theorem liftIndep_pow_j (hA : A.LiesOverPrime q)
    (hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hpin : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hOy : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hOy⟩ : qExpFunctionFieldC (ResidueField A)
              (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y)
    (j : fieldBar q M') (hj : j ∈ R.integers)
    (hjc : ((R.residue ⟨j, hj⟩ : qExpFunctionFieldC (ResidueField A)
          (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) : LaurentSeries (ResidueField A)).coeff (-1) ≠ 0)
    (c : Fin q → KB q M') (hc : ∀ m, algebraMap (KB q M') (fieldBar q M') (c m) ∈ R.integers)
    (hlt : R.integers.valuation (∑ m, algebraMap (KB q M') (fieldBar q M') (c m) * j ^ (m : ℕ)) < 1) :
    ∀ m, R.integers.valuation (algebraMap (KB q M') (fieldBar q M') (c m)) < 1 := by
  classical
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA

  have hres := fun m => residue_algebraMap_KB_eq_qExpand q M' A R hA hR hpin (c m) (hc m)
  choose e heE0 he using hres

  let cO : Fin q → R.integers := fun m => ⟨algebraMap (KB q M') (fieldBar q M') (c m), hc m⟩
  let jO : R.integers := ⟨j, hj⟩
  have hsum0 : R.residue (∑ m, cO m * jO ^ (m : ℕ)) = 0 := by
    rw [← valuation_lt_one_iff_residue_eq_zero q M' A R, coe_sum_mul_pow q M' A R]
    exact hlt
  rw [residue_sum_mul_pow q M' A R] at hsum0

  have hser : ∑ m, qExpand (ResidueField A) q (e m) *
      ((R.residue jO : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))) :
        LaurentSeries (ResidueField A)) ^ (m : ℕ) = 0 := by
    have h := congrArg Subtype.val hsum0
    rw [ZeroMemClass.coe_zero, coe_residue_sum_mul_pow q M' A] at h
    rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← he m]
  have hzero := qExpand_linearIndependent_pow q (ResidueField A) _ hjc e hser
  intro m
  have hm : R.residue (cO m) = 0 := by
    apply Subtype.ext
    rw [he m, hzero m, map_zero, ZeroMemClass.coe_zero]
  exact (valuation_lt_one_iff_residue_eq_zero q M' A R (cO m)).mpr hm

end Assembly

end ModularCurve.FullLevel.BorelGauss
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve.FullLevel.BorelGauss"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve"

open ModularCurve.FullLevel.BorelGauss in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hfix : redQ q δ • lineInfty q = lineInfty q) :
    O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O := by
  classical
  haveI : Fact (¬ q ∣ M') := ⟨hqM'⟩
  have hc : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := ModularCurve.FullLevel.BorelGauss.dvd_of_redQ_smul_lineInfty_eq q δ hfix
  obtain ⟨R, hRO, hpin⟩ := exists_regularProlongation_integers_eq q M' A O hO
  have hR : ∀ f : fieldBar q M', f ∈ R.integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
    intro f; rw [hRO]; exact hO f
  obtain ⟨j, hjO, -, hjc, -⟩ := exists_j q M' A R hA hR hpin

  let b : Fin q → fieldBar q M' := fun m => j ^ ((m : Fin q) : ℕ)
  have hb : ∀ m, b m ∈ O := fun m => by
    rw [← hRO]; exact pow_mem hjO _
  refine comap_levelAutBar_eq_of_family q M' hq2 ζ δ hδ hc O b hb ?_ ?_
  ·
    intro c hcO hlt m
    have hc'' : ∀ m, algebraMap (KB q M') (fieldBar q M') (c m) ∈ R.integers := fun m => by
      rw [hRO]; exact hcO m
    have key := liftIndep_pow_j q M' A R hA hR hpin j hjO hjc c hc'' (by rw [hRO]; exact hlt) m
    rwa [hRO] at key
  ·
    rw [Fintype.card_fin, hq2]
    norm_num

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two.ModularCurve.FullLevel.BorelGauss"

end S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two (solution)
