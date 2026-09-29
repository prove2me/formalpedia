-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_twoMembers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/02d433bb-cef5-5bc5-beaf-9ef57e961851

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_modulusExp
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.ModularCurve.MultCovering"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord Place.ord_zero Place.ord_inv HasPrincipalDivisors Place.evalAt_one prox evalVec Place.mem_of_ord_nonneg Annulus.residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends prox_eq_neg_log_iSup_sub_of_chart exists_evalVec_eq_smul_mulVec_of_eq_sum_smul prox_smul_smul abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le Place.isRational_of_isAlgClosed Place.ord_finset_prod'"
p2m_open "AlgebraicCurve"

private theorem abv_sub_le_max {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (a b : L) :
    μ (a - b) ≤ max (μ a) (μ b) := by
  rcases le_total (μ b) (μ a) with hab | hab
  ·
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero] at hab
      have hb : b = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg b))
      simp [hb]
    have hq : b * a⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos ha0)).2 (by simpa using hab))
    have h1 : 1 - b * a⁻¹ ∈ A := sub_mem (one_mem _) hq
    have h2 : μ (1 - b * a⁻¹) ≤ 1 := (hμA _).1 h1
    have : a - b = a * (1 - b * a⁻¹) := by field_simp
    rw [this, map_mul]
    calc μ a * μ (1 - b * a⁻¹) ≤ μ a * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg a)
      _ = μ a := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_left _ _
  · rcases eq_or_ne b 0 with rfl | hb0
    · rw [map_zero] at hab
      have ha : a = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg a))
      simp [ha]
    have hq : a * b⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos hb0)).2 (by simpa using hab))
    have h1 : a * b⁻¹ - 1 ∈ A := sub_mem hq (one_mem _)
    have h2 : μ (a * b⁻¹ - 1) ≤ 1 := (hμA _).1 h1
    have : a - b = b * (a * b⁻¹ - 1) := by field_simp
    rw [this, map_mul]
    calc μ b * μ (a * b⁻¹ - 1) ≤ μ b * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg b)
      _ = μ b := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_right _ _

private theorem abv_eq_one_of_isUnit_vs {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : μ a = 1 := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : a * (b : L) = 1 := by
    have := congrArg (fun t : A => (t : L)) hb
    simpa using this
  have h1 : μ a * μ (b : L) = 1 := by rw [← map_mul, hb', map_one]
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  have hb1 : μ (b : L) ≤ 1 := (hμA (b : L)).1 b.2
  have ha0 : 0 ≤ μ a := μ.nonneg a
  exact le_antisymm ha1 (by nlinarith)

private theorem abv_lt_one_of_mem_maximalIdeal_vs {L : Type*} [Field L]
    {A : ValuationSubring L} (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L}
    (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) : μ a < 1 := by
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  refine lt_of_le_of_ne ha1 fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at h1
  have hinv : a⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

private theorem residue_eq_zero_of_mem_maximalIdeal' {L : Type*} [Field L] {A : ValuationSubring L}
    {a : L} (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing.residue A ⟨a, ha⟩ = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).2 hm

private theorem abv_evalAt_eq_zpow_of_isAttached
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar)
    (hatt : An.IsAttached C x) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, 0 < μ (Q.evalAt An.param) ∧ μ (Q.evalAt An.param) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by
  intro Q hQ
  obtain ⟨-, hzC, -, hlaw⟩ := hatt
  obtain ⟨hw, hunit⟩ := hlaw f hf hres hzf Q hQ
  obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, -⟩ := An.mem_dom Q hQ
  have hμz1 : μ (Q.evalAt An.param) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
  have hμz0 : 0 < μ (Q.evalAt An.param) := μ.pos hz0
  have hunit1 := abv_eq_one_of_isUnit_vs μ hμA hw hunit
  rw [map_mul, map_zpow₀, zpow_neg] at hunit1
  exact ⟨hμz0, hμz1, (mul_inv_eq_one₀ (zpow_ne_zero _ hμz0.ne')).1 hunit1⟩

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one mem_of_ord_nonneg isRational_of_isAlgClosed ord_finset_prod'" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_sub' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    (∏ i ∈ S, f i) ∈ v.toValuationSubring ∧ v.evalAt (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨by simp, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨hmem, heq⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hi]; exact mul_mem hfi hmem
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, v.evalAt_mul' hv hfi hmem, heq]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul' hv (pow_mem hf n) hf, ih]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_neg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) : v.ord (-f) = v.ord f := by
  unfold Place.ord
  rw [Valuation.map_neg]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {ι : Type*} (S : Finset ι) (f : ι → F) (hf : ∀ i ∈ S, f i ≠ 0) :
    v.ord (∏ i ∈ S, f i) = ∑ i ∈ S, v.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' _
  have h1 : 0 ≤ v.ord (algebraMap K F c) := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem) with h | h
    · simp [h]
    · exact h
  have h2 : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem') with h | h
    · simp [h]
    · exact h
  rw [v.ord_inv] at h2
  omega

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.isUnit_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hf⟩ : v.toValuationSubring) = u := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_eq_zero_of_evalAt_ne_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (v.ord_nonneg_of_mem' hf) (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

private theorem inv_mem_of_isUnit' {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers placeMap residue pointwise ker_residue dom" end ComponentChart
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.isUnit_of_residue_ne_zero'"
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_inv'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_inv'"
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar nCharts mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom hasseExp_le_modulusExp goodFamily_zero_eq_one infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec"
p2m_open "ModularCurve.MultCovering ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve IsLocalRing"

section GenericHelpers

theorem evalAt_mul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_algebraMap_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

theorem minor_mulVec_D {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end GenericHelpers

section FamilyFacts
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)

theorem goodFamily_ne_zero' (i : Fin r) : goodFamily Φ i ≠ 0 := Φ.t_basis.1.ne_zero i

theorem goodFamilyZero_eq_inv_mul' (l : Fin r) :
    goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * goodFamily Φ l := rfl

end FamilyFacts

section CtxFacts
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
  (Γ : ChartCtx p A) (Δ : AnnCtx Γ)

theorem modulus_dvd' (e : Fin (mAnnuli p)) : ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  have hw : jWidth (ssValue Γ e) ≤ 3 := by
    unfold jWidth; split_ifs <;> norm_num
  refine ⟨(p : AlgebraicClosure ℚ) ^ (3 - jWidth (ssValue Γ e)), pow_mem (natCast_mem A p) _, ?_⟩
  have hm : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  rw [hm, ← pow_add, show modulusExp = 3 from rfl, Nat.add_sub_cancel' hw]

end CtxFacts

theorem annOut_wide' (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
        μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  intro μ hμA
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA
  refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
  have key : ∀ Q ∈ (Δ.annIn e).dom,
      μ (Q.evalAt (Δ.annOut e).param) * μ (Q.evalAt (Δ.annIn e).param)
        = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) := by
    intro Q hQ
    obtain ⟨hrat, hzin, -, hz0, -⟩ := (Δ.annIn e).mem_dom Q hQ
    obtain ⟨-, hzout, -⟩ := (Δ.annOut e).mem_dom Q (hdom ▸ hQ)
    rw [← map_mul, ← evalAt_mul_D Q hrat hzout hzin, htwo, evalAt_algebraMap_D]
  intro heq
  apply hne
  have h1 := key Q₁ hQ₁
  have h2 := key Q₂ hQ₂
  rw [heq] at h1
  have h12 := h1.trans h2.symm
  have hne0 : μ (Q₂.evalAt (Δ.annOut e).param) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (μ.pos hmod0).ne' h2.symm
  exact mul_left_cancel₀ hne0 h12

end ModularCurve.MultCovering

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar nCharts mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom hasseExp_le_modulusExp goodFamily_zero_eq_one infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec"
p2m_open "ModularCurve.MultCovering ModularCurve"
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve IsLocalRing"

theorem isRational_Fbar {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (i : Fin nCharts)
    (x : Place (IsLocalRing.ResidueField ↥A) (Fbar A i)) : x.IsRational := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  let eqv := ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)
  letI : Algebra (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A i) := eqv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A i) :=
    IsScalarTower.of_algebraMap_eq fun c => (eqv.commutes c).symm
  haveI : FiniteDimensional (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A i) := by
    let L : RatFunc (IsLocalRing.ResidueField ↥A) ≃ₗ[RatFunc (IsLocalRing.ResidueField ↥A)] Fbar A i :=
      { eqv.toRingEquiv.toAddEquiv with
        map_smul' := fun r y => by
          show eqv (r * y) = eqv r * eqv y
          exact map_mul eqv r y }
    exact L.finiteDimensional
  exact Place.isRational_of_isAlgClosed _

theorem zeroFree_or_exists_unique_zero_of_ord_one_of_ord_zeroChart_le_zero (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : (AlgebraicClosure ℚ), a ∈ A ↔ μ a ≤ 1)
    (l : Fin r) (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hβ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) ≤ 0)
    (hreg : ∀ Q ∈ (Δ.annIn e).dom, goodFamily Φ l ∈ Q.toValuationSubring) :
    (∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) = 0) ∨
    ∃ Ql ∈ (Δ.annIn e).dom, (∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 → Q = Ql) ∧
      0 < Ql.ord (goodFamily Φ l) ∧
      μ (Ql.evalAt (Δ.annOut e).param) = μ ((p : (AlgebraicClosure ℚ))) ^ hasseExp Φ.toFamData l := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hattOut := Δ.attached_tgt e
  have hattIn := Δ.attached_src e
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hintI, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  have hintC : goodFamily Φ l ∈ (chart Γ (tgt p e)).integers := hint
  have hres : (chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hintC⟩ ≠ 0 := hresI l
  set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l with hc'
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem (natCast_mem A p) _
  have heqZ : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l = goodFamilyZero Φ.toFamData l := rfl
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l ∈ (chart Γ (src p e)).integers := by
    rw [heqZ]; exact hintZ l
  have eZ : (⟨_, hC'⟩ : (chart Γ (src p e)).integers) = ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ := Subtype.ext heqZ
  have hres' : (chart Γ (src p e)).residue ⟨_, hC'⟩ ≠ 0 := by rw [eZ]; exact hresZ l
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l) := by
    intro Q hQ; rw [hdom] at hQ; exact Place.ord_nonneg_of_mem' Q (hreg Q hQ)
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hmod0' : ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) := by
    rw [mul_comm (Δ.annIn e).param, hmod]; exact htwo
  obtain ⟨D, hD0, hDdom, hDord, hDsum, hDlog⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' (chart Γ (tgt p e)) (nodeTgt Γ e) hattOut
      (chart Γ (src p e)) (nodeSrc Γ e) hattIn hwide (goodFamily Φ l) hintC hres c' hc'0 hc'A hC' hres' hpole
  have hord' : (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hintC⟩) = 1 := hord
  have hβ' : (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, hC'⟩) ≤ 0 := by rw [eZ]; exact hβ
  obtain ⟨hsum0, -, -⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' (chart Γ (tgt p e)) (nodeTgt Γ e) hattOut
      (chart Γ (src p e)) (nodeSrc Γ e) hattIn hwide (goodFamily Φ l) hintC hres c' hc'0 hc'A hC' hres' hpole
  rw [hord'] at hDsum hsum0
  have hsumZ : (D.sum fun _ m => m : ℤ) = ∑ Q ∈ D.support, D Q := rfl
  by_cases hzero : (D.sum fun _ m => m : ℤ) = 0
  ·
    left
    intro Q hQ
    have hQ' : Q ∈ (Δ.annOut e).dom := by rw [hdom]; exact hQ
    rw [← hDord Q hQ']
    by_contra hne
    have hpos : 0 < D Q := lt_of_le_of_ne (hD0 Q) (Ne.symm hne)
    have : 0 < (D.sum fun _ m => m : ℤ) := by
      rw [hsumZ]; exact Finset.sum_pos' (fun P _ => hD0 P) ⟨Q, Finsupp.mem_support_iff.2 hne, hpos⟩
    omega
  ·
    right
    have hone : (D.sum fun _ m => m : ℤ) = 1 := by omega
    have hβ0 : (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, hC'⟩) = 0 := by omega
    rw [hβ0, Int.cast_zero, zero_mul, add_zero] at hDlog
    have hne : D.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h0
      rw [hsumZ, h0, Finset.sum_empty] at hone; exact zero_ne_one hone
    obtain ⟨Ql, hQl⟩ := hne
    have hQl0 : D Ql ≠ 0 := Finsupp.mem_support_iff.1 hQl
    have hsupp : D.support = {Ql} := by
      apply Finset.eq_singleton_iff_unique_mem.2 ⟨hQl, fun Q hQ => ?_⟩
      by_contra hne'
      have hQ0 : D Q ≠ 0 := Finsupp.mem_support_iff.1 hQ
      have h1 : 1 ≤ D Q := by have := hD0 Q; omega
      have h2 : 1 ≤ D Ql := by have := hD0 Ql; omega
      have hsub : ({Q, Ql} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))) ⊆ D.support := by
        intro P hP; rcases Finset.mem_insert.1 hP with rfl | hP; exact hQ; rw [Finset.mem_singleton.1 hP]; exact hQl
      have hle : ∑ P ∈ ({Q, Ql} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))), D P ≤ ∑ P ∈ D.support, D P :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => hD0 P)
      rw [Finset.sum_pair hne', ← hsumZ, hone] at hle
      omega
    have hDQl : D Ql = 1 := by
      rw [hsumZ, hsupp, Finset.sum_singleton] at hone; exact hone
    have hQld : Ql ∈ (Δ.annOut e).dom := hDdom Ql hQl0
    have hQld' : Ql ∈ (Δ.annIn e).dom := by rw [← hdom]; exact hQld
    refine ⟨Ql, hQld', ?_, ?_, ?_⟩
    · intro Q hQ hne0
      have hQ' : Q ∈ (Δ.annOut e).dom := by rw [hdom]; exact hQ
      have hDQ : D Q ≠ 0 := by rw [hDord Q hQ']; exact hne0
      have := Finsupp.mem_support_iff.2 hDQ
      rw [hsupp, Finset.mem_singleton] at this
      exact this
    · rw [← hDord Ql hQld, hDQl]; exact one_pos
    · rw [Finsupp.sum, hsupp, Finset.sum_singleton, hDQl, Int.cast_one, one_mul, hc', map_pow] at hDlog
      obtain ⟨-, -, -, hz0, -⟩ := (Δ.annOut e).mem_dom Ql hQld
      exact Real.log_injOn_pos (Set.mem_Ioi.2 (μ.pos hz0)) (Set.mem_Ioi.2 (pow_pos (μ.pos hp0) _)) hDlog

theorem isUnit_evalAt_goodFamilyZero_of_abv_lt (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : (AlgebraicClosure ℚ), a ∈ A ↔ μ a ≤ 1)
    (l : Fin r) (hl : 1 ≤ (l : ℕ)) (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hβ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0)
    (Ql : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hQl : Ql ∈ (Δ.annIn e).dom)
    (huniq : ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 → Q = Ql) (hQlpos : 0 < Ql.ord (goodFamily Φ l))
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hR : R ∈ (Δ.annIn e).dom)
    (hbelow : μ (R.evalAt (Δ.annOut e).param) < μ (Ql.evalAt (Δ.annOut e).param)) :
    ∃ h : R.evalAt (goodFamilyZero Φ.toFamData l) ∈ A, IsUnit (⟨_, h⟩ : ↥A) ∧
      IsLocalRing.residue ↥A ⟨_, h⟩ = (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : (AlgebraicClosure ℚ)) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hattOut := Δ.attached_tgt e
  have hattIn := Δ.attached_src e
  have hattOut' := Δ.attached_tgt e
  have hattIn' := Δ.attached_src e
  obtain ⟨-, hzoC, hzoord, -⟩ := hattOut'
  obtain ⟨-, hziC, hziord, -⟩ := hattIn'
  set C0 := (chart Γ (src p e)) with hC0_def
  set Cinf := (chart Γ (tgt p e)) with hCinf_def
  set xs := nodeSrc Γ e with hxs_def
  set xt := (nodeTgt Γ e) with hxt_def
  set zi := (Δ.annIn e).param with hzi_def
  set zo := (Δ.annOut e).param with hzo_def
  set n : ℕ := hasseExp Φ.toFamData l with hn_def
  set w : ℕ := jWidth (ssValue Γ e) with hw_def
  have hint0C : (goodFamilyZero Φ.toFamData l) ∈ C0.integers := hint0
  have hintC : goodFamily Φ l ∈ Cinf.integers := hint
  obtain ⟨hintI, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have ht'res0 : C0.residue ⟨(goodFamilyZero Φ.toFamData l), hint0C⟩ ≠ 0 := hresZ l
  have htres0 : Cinf.residue ⟨goodFamily Φ l, hintC⟩ ≠ 0 := hresI l
  have hzires0 : C0.residue ⟨zi, hziC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hziord; exact zero_ne_one hziord
  have hzores0 : Cinf.residue ⟨zo, hzoC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzoord; exact zero_ne_one hzoord
  have hzi0 : zi ≠ 0 := by
    intro h0; apply hzires0
    have : (⟨zi, hziC⟩ : C0.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hzo0 : zo ≠ 0 := by
    intro h0; apply hzores0
    have : (⟨zo, hzoC⟩ : Cinf.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hπ : (((Δ.annIn e).modulus : ↥A) : (AlgebraicClosure ℚ)) = (p : (AlgebraicClosure ℚ)) ^ w := by
    show (((Δ.An e).modulus : ↥A) : (AlgebraicClosure ℚ)) = _
    rw [Δ.modulus_eq e]; norm_cast
  have hzz : zo * zi = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ w) := by rw [← hπ]; exact htwo
  have hαp : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) ≠ 0 := (map_ne_zero _).2 hp0
  have hzi_eq : zi = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ w) * zo⁻¹ := by
    rw [← hzz]; field_simp

  set h : (modularFunctionFieldBar (1 * p)) := (goodFamilyZero Φ.toFamData l) * zi ^ n with hh_def
  have hhC : h ∈ C0.integers := mul_mem hint0C (pow_mem hziC _)
  have hhres : C0.residue ⟨h, hhC⟩ = C0.residue ⟨(goodFamilyZero Φ.toFamData l), hint0C⟩ * (C0.residue ⟨zi, hziC⟩) ^ n := by
    have e1 : (⟨h, hhC⟩ : C0.integers) = ⟨(goodFamilyZero Φ.toFamData l), hint0C⟩ * ⟨zi, hziC⟩ ^ n := Subtype.ext rfl
    rw [e1, map_mul, map_pow]
  have hhres0 : C0.residue ⟨h, hhC⟩ ≠ 0 := by rw [hhres]; exact mul_ne_zero ht'res0 (pow_ne_zero _ hzires0)
  have hhord : xs.ord (C0.residue ⟨h, hhC⟩) = n := by
    rw [hhres, xs.ord_mul ht'res0 (pow_ne_zero _ hzires0), ← zpow_natCast, xs.ord_zpow]
    have h1 : xs.ord (C0.residue ⟨(goodFamilyZero Φ.toFamData l), hint0C⟩) = 0 := hβ
    have h2 : xs.ord (C0.residue ⟨zi, hziC⟩) = 1 := hziord
    rw [h1, h2]; ring

  have hw1 : 1 ≤ w := by rw [hw_def]; unfold jWidth; split_ifs <;> norm_num
  set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ (n * (w - 1)) with hc'
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem hpA _
  have hzounit : IsUnit (⟨zo, hzoC⟩ : Cinf.integers) := Cinf.isUnit_of_residue_ne_zero' hzoC hzores0
  have hzoinvC : zo⁻¹ ∈ Cinf.integers := inv_mem_of_isUnit' hzoC hzounit
  have hident : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * h = goodFamily Φ l * (zo⁻¹) ^ n := by
    have et : (goodFamilyZero Φ.toFamData l) = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ n))⁻¹ * goodFamily Φ l := rfl
    rw [hh_def, et, hzi_eq, hc', mul_pow, ← map_pow]
    have hsplit : ((p : (AlgebraicClosure ℚ)) ^ w) ^ n = (p : (AlgebraicClosure ℚ)) ^ (n * (w - 1)) * (p : (AlgebraicClosure ℚ)) ^ n := by
      rw [← pow_mul, ← pow_add]; congr 1
      obtain ⟨w', hw'⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      rw [hw', Nat.add_sub_cancel]; ring
    rw [hsplit, map_mul]
    have h1 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ (n * (w - 1))) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp0)
    have h2 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ n) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp0)
    field_simp
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * h ∈ Cinf.integers := by
    rw [hident]; exact mul_mem hintC (pow_mem hzoinvC _)
  have hres' : Cinf.residue ⟨_, hC'⟩ ≠ 0 := by
    have e1 : (⟨_, hC'⟩ : Cinf.integers) = ⟨goodFamily Φ l, hintC⟩ * ⟨zo⁻¹, hzoinvC⟩ ^ n := Subtype.ext hident
    rw [e1, map_mul, map_pow, Cinf.residue_inv' hzoC hzores0 hzoinvC]
    exact mul_ne_zero htres0 (pow_ne_zero _ (inv_ne_zero hzores0))

  have htreg : ∀ Q ∈ (Δ.annIn e).dom, goodFamily Φ l ∈ Q.toValuationSubring := fun Q hQ =>
    (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e Q hQ l hl).1
  have hordzi : ∀ Q ∈ (Δ.annIn e).dom, Q.ord zi = 0 := by
    intro Q hQ
    obtain ⟨-, hzQ, -, hzQ0, -⟩ := (Δ.annIn e).mem_dom Q hQ
    exact Place.ord_eq_zero_of_evalAt_ne_zero' Q hzQ hzQ0
  have ht'ord : ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamilyZero Φ.toFamData l) = Q.ord (goodFamily Φ l) := by
    intro Q hQ
    have et : (goodFamilyZero Φ.toFamData l) = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ n))⁻¹ * goodFamily Φ l := rfl
    rw [et, Q.ord_mul (inv_ne_zero ((map_ne_zero _).2 (pow_ne_zero _ hp0))) (Φ.t_basis.1.ne_zero l), Place.ord_inv,
      Place.ord_algebraMap' Q (pow_ne_zero _ hp0)]
    ring
  have ht'0 : (goodFamilyZero Φ.toFamData l) ≠ 0 := by
    intro h0; apply ht'res0
    have : (⟨(goodFamilyZero Φ.toFamData l), hint0C⟩ : C0.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hhord' : ∀ Q ∈ (Δ.annIn e).dom, Q.ord h = Q.ord (goodFamily Φ l) := by
    intro Q hQ
    rw [hh_def, Q.ord_mul ht'0 (pow_ne_zero _ hzi0), Place.ord_pow', hordzi Q hQ, ht'ord Q hQ]; ring
  have hpole : ∀ Q ∈ (Δ.annIn e).dom, 0 ≤ Q.ord h := fun Q hQ => by
    rw [hhord' Q hQ]; exact Place.ord_nonneg_of_mem' Q (htreg Q hQ)

  set D : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) →₀ ℤ := Finsupp.single Ql (Ql.ord (goodFamily Φ l)) with hD_def
  have hD0 : ∀ Q, 0 ≤ D Q := by
    intro Q; rw [hD_def, Finsupp.single_apply]; split_ifs; exact hQlpos.le; exact le_rfl
  have hDdom : ∀ Q, D Q ≠ 0 → Q ∈ (Δ.annIn e).dom := by
    intro Q hQ; rw [hD_def, Finsupp.single_apply] at hQ
    split_ifs at hQ with h1
    · rw [← h1]; exact hQl
    · exact absurd rfl hQ
  have hD : ∀ Q ∈ (Δ.annIn e).dom, D Q = Q.ord h := by
    intro Q hQ
    rw [hhord' Q hQ, hD_def, Finsupp.single_apply]
    split_ifs with h1
    · rw [h1]
    · by_contra hne
      exact h1 (huniq Q hQ (Ne.symm hne)).symm

  have hwide := Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA
  have hx : xs.IsRational := isRational_Fbar (p := p) (src p e) _

  obtain ⟨hRrat, hziR, -, hziR0, -⟩ := (Δ.annIn e).mem_dom R hR
  obtain ⟨hQlrat, hziQl, -, hziQl0, -⟩ := (Δ.annIn e).mem_dom Ql hQl
  have hprodR : ∀ P ∈ (Δ.annIn e).dom, P.evalAt zo * P.evalAt zi = (p : (AlgebraicClosure ℚ)) ^ w := by
    intro P hP
    obtain ⟨hPrat, hziP, -⟩ := (Δ.annIn e).mem_dom P hP
    obtain ⟨-, hzoP, -⟩ := (Δ.annOut e).mem_dom P (by rw [hdom]; exact hP)
    rw [← Place.evalAt_mul' P hPrat hzoP hziP, hzz, Place.evalAt_algebraMap']
  have hcritR : μ (Ql.evalAt zi) < μ (R.evalAt zi) := by
    have hpw : 0 < μ ((p : (AlgebraicClosure ℚ)) ^ w) := by rw [map_pow]; exact pow_pos (μ.pos hp0) _
    have e1 := hprodR R hR
    have e2 := hprodR Ql hQl
    obtain ⟨-, -, -, hzoR0, -⟩ := (Δ.annOut e).mem_dom R (by rw [hdom]; exact hR)
    obtain ⟨-, -, -, hzoQ0, -⟩ := (Δ.annOut e).mem_dom Ql (by rw [hdom]; exact hQl)
    have hR1 : μ (R.evalAt zi) = μ ((p : (AlgebraicClosure ℚ)) ^ w) / μ (R.evalAt zo) := by
      rw [← e1, map_mul, mul_div_cancel_left₀ _ (μ.pos hzoR0).ne']
    have hQ1 : μ (Ql.evalAt zi) = μ ((p : (AlgebraicClosure ℚ)) ^ w) / μ (Ql.evalAt zo) := by
      rw [← e2, map_mul, mul_div_cancel_left₀ _ (μ.pos hzoQ0).ne']
    rw [hR1, hQ1]
    exact div_lt_div_of_pos_left hpw (μ.pos hzoR0) hbelow
  have hcrit : ∀ Q, D Q ≠ 0 → μ (Q.evalAt zi) ≠ μ (R.evalAt zi) := by
    intro Q hQ
    rw [hD_def, Finsupp.single_apply] at hQ
    split_ifs at hQ with h1
    · rw [← h1]; exact hcritR.ne
    · exact absurd rfl hQ

  obtain ⟨hmem, hunit, hresid⟩ :=
    AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_mul_eq_of_isAttached_both_ends_of_forall_abv_ne μ hμA
      (Δ.annIn e) (Δ.annOut e) hdom hmod hmod0 htwo C0 xs hattIn hx Cinf xt hattOut hwide
      h hhC hhres0 c' hc'0 hc'A hC' hres' hpole hziC D hD0 hDdom hD R hR hcrit

  have hN : (D.sum fun Q m => if μ (R.evalAt zi) < μ (Q.evalAt zi) then m else 0) = 0 := by
    rw [hD_def, Finsupp.sum_single_index (by simp)]
    rw [if_neg (not_lt.2 hcritR.le)]
  have hc1 : (D.prod fun Q m => if μ (R.evalAt zi) < μ (Q.evalAt zi) then (-(Q.evalAt zi)) ^ m else 1) = 1 := by
    rw [hD_def, Finsupp.prod_single_index (by simp)]
    rw [if_neg (not_lt.2 hcritR.le)]

  have ht'R : (goodFamilyZero Φ.toFamData l) ∈ R.toValuationSubring := by
    have et : (goodFamilyZero Φ.toFamData l) = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ n))⁻¹ * goodFamily Φ l := rfl
    rw [et, ← map_inv₀]; exact mul_mem (R.algebraMap_mem' _) (htreg R hR)
  have hval : R.evalAt h * (R.evalAt zi) ^ (-(xs.ord (C0.residue ⟨h, hhC⟩)
        - (D.sum fun Q m => if μ (R.evalAt zi) < μ (Q.evalAt zi) then m else 0)))
      * (D.prod fun Q m => if μ (R.evalAt zi) < μ (Q.evalAt zi) then (-(Q.evalAt zi)) ^ m else 1)⁻¹
      = R.evalAt (goodFamilyZero Φ.toFamData l) := by
    rw [hN, hc1, inv_one, mul_one, sub_zero, hhord, hh_def, Place.evalAt_mul' R hRrat ht'R (pow_mem hziR _),
      Place.evalAt_pow' R hRrat hziR, zpow_neg, zpow_natCast, mul_inv_cancel_right₀ (pow_ne_zero _ hziR0)]
  have hA' : R.evalAt (goodFamilyZero Φ.toFamData l) ∈ A := hval ▸ hmem
  have eA : (⟨_, hmem⟩ : ↥A) = ⟨R.evalAt (goodFamilyZero Φ.toFamData l), hA'⟩ := Subtype.ext hval
  refine ⟨hA', eA ▸ hunit, ?_⟩
  rw [← eA, hresid, hhord, hhres]

  congr 1
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hzires0, add_neg_cancel, zpow_zero, mul_one]
  rfl

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar nCharts mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom hasseExp_le_modulusExp goodFamily_zero_eq_one infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec"
p2m_open "ModularCurve.MultCovering ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve IsLocalRing"

section ResidueLinePort

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ord_charLGeomPlaceOfPoint_jBar_sub' (k : Type) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord (jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c) = if c = a then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a c

theorem jBar_sub_algebraMap_ne_zero' (k : Type) [Field k] [DecidableEq k] (c : k) :
    jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jBar_sub' k c c
  rw [h, Place.ord_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem jBar_ne_zero' (k : Type) [Field k] [DecidableEq k] : jBar k ≠ 0 := by
  simpa using jBar_sub_algebraMap_ne_zero' k 0

private theorem _root_.AlgebraicCurve.Place.ord_finset_prod' {K F : Type*} [Field K] [Field F] [Algebra K F]
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

p2m_alias "P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve.Place.ord_finset_prod'" "AlgebraicCurve.Place.ord_finset_prod'"
theorem ssPolyBar_ne_zero' : ssPolyBar Γ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun e _ => jBar_sub_algebraMap_ne_zero' _ _

theorem ord_nodeTgt_ssPolyBar' (e : Fin (mAnnuli p)) : (nodeTgt Γ e).ord (ssPolyBar Γ) = 1 := by
  show (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord _ = 1
  rw [ssPolyBar, Place.ord_finset_prod' _ _ _ (fun e' _ => jBar_sub_algebraMap_ne_zero' _ _)]
  simp_rw [ord_charLGeomPlaceOfPoint_jBar_sub', (ssValue_injective Γ).eq_iff]
  simp [Finset.sum_ite_eq']

theorem ord_nodeTgt_jBar' (e : Fin (mAnnuli p)) :
    (nodeTgt Γ e).ord (jBar (IsLocalRing.ResidueField ↥A)) = if (0 : IsLocalRing.ResidueField ↥A) = ssValue Γ e then 1 else 0 := by
  have h := ord_charLGeomPlaceOfPoint_jBar_sub' (IsLocalRing.ResidueField ↥A) (ssValue Γ e) 0
  rw [map_zero, sub_zero] at h
  exact h

theorem nodeTgt_isRational' (e : Fin (mAnnuli p)) : (nodeTgt Γ e).IsRational := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  let eqv := ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)
  letI : Algebra (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) := eqv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) :=
    IsScalarTower.of_algebraMap_eq fun c => (eqv.commutes c).symm
  haveI : FiniteDimensional (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) := by
    let L : RatFunc (IsLocalRing.ResidueField ↥A) ≃ₗ[RatFunc (IsLocalRing.ResidueField ↥A)] Fbar A (tgt p e) :=
      { eqv.toRingEquiv.toAddEquiv with
        map_smul' := fun r y => by
          show eqv (r * y) = eqv r * eqv y
          exact map_mul eqv r y }
    exact L.finiteDimensional
  exact Place.isRational_of_isAlgClosed _

end ResidueLinePort

end ModularCurve.MultCovering

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar nCharts mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom hasseExp_le_modulusExp goodFamily_zero_eq_one infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec"
p2m_open "ModularCurve.MultCovering ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve IsLocalRing"

section TubeSepTangent

private theorem abv_sub_eq_of_abv_lt {L : Type*} [Field L] (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ)
    {a b : L} (h : μ b < μ a) : μ (a - b) = μ a := by
  apply le_antisymm
  · have := hμ a (-b)
    rw [← sub_eq_add_neg, μ.map_neg] at this
    exact this.trans (max_le le_rfl h.le)
  · have := hμ (a - b) b
    rw [sub_add_cancel] at this
    rcases le_max_iff.1 this with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 h)

private theorem Place.evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem aeval_jBar_mem_and_evalAt {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (e : Fin (mAnnuli p))
    (q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) q ∈ (nodeTgt Γ e).toValuationSubring ∧
    (nodeTgt Γ e).evalAt (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) q) = q.eval (ssValue Γ e) := by
  have hxrat := nodeTgt_isRational' Γ e
  have hjreg : jBar (IsLocalRing.ResidueField ↥A) ∈ (nodeTgt Γ e).toValuationSubring :=
    Place.mem_of_ord_nonneg _ (jBar_ne_zero' _) (by rw [ord_nodeTgt_jBar']; split_ifs <;> norm_num)
  have hjval : (nodeTgt Γ e).evalAt (jBar (IsLocalRing.ResidueField ↥A)) = ssValue Γ e := by
    have hpos : (nodeTgt Γ e).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e)) = 1 := by
      have h := ord_charLGeomPlaceOfPoint_jBar_sub' (IsLocalRing.ResidueField ↥A) (ssValue Γ e) (ssValue Γ e)
      rw [if_pos rfl] at h
      exact h
    have hreg : jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e) ∈ (nodeTgt Γ e).toValuationSubring :=
      sub_mem hjreg ((nodeTgt Γ e).algebraMap_mem' _)
    have h0 : (nodeTgt Γ e).evalAt (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e)) = 0 := by
      by_contra hne
      have := Place.ord_eq_zero_of_evalAt_ne_zero' _ hreg hne
      exact zero_ne_one (this.symm.trans hpos)
    rw [Place.evalAt_sub' _ hxrat hjreg ((nodeTgt Γ e).algebraMap_mem' _), Place.evalAt_algebraMap', sub_eq_zero] at h0
    exact h0
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    exact ⟨(nodeTgt Γ e).algebraMap_mem' _, Place.evalAt_algebraMap' _ _⟩
  | add f g hf hg =>
    rw [map_add, Polynomial.eval_add]
    exact ⟨add_mem hf.1 hg.1, by rw [Place.evalAt_add' _ hxrat hf.1 hg.1, hf.2, hg.2]⟩
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_X]
    exact ⟨mul_mem h.1 hjreg, by rw [Place.evalAt_mul' _ hxrat h.1 hjreg, h.2, hjval]⟩

theorem tubeMember_value_D (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : (AlgebraicClosure ℚ), a ∈ A ↔ μ a ≤ 1)
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hR : R ∈ (Δ.annIn e).dom) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hout : ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
      μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param))
    (hint : goodFamily Φ l ∈ (chart Γ (tgt p e)).integers) (hzoC : (Δ.annOut e).param ∈ (chart Γ (tgt p e)).integers) :
    ∃ hmem : R.evalAt (goodFamily Φ l) * (R.evalAt (Δ.annOut e).param)
        ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩))) ∈ A,
      IsUnit (⟨_, hmem⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hmem⟩ = (nodeTgt Γ e).evalAt ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩
        * ((chart Γ (tgt p e)).residue ⟨(Δ.annOut e).param, hzoC⟩) ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩)))) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hattOut := Δ.attached_tgt e
  have hattIn := Δ.attached_src e
  obtain ⟨hintI, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have hres : (chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩ ≠ 0 := hresI l
  set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l with hc'
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem (natCast_mem A p) _
  have heqZ : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l = goodFamilyZero Φ.toFamData l := by
    rw [goodFamilyZero_eq_inv_mul']
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l ∈ (chart Γ (src p e)).integers := by
    rw [heqZ]; exact hintZ l
  have hres' : (chart Γ (src p e)).residue ⟨_, hC'⟩ ≠ 0 := by
    have e1 : (⟨_, hC'⟩ : (chart Γ (src p e)).integers) = ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ := Subtype.ext heqZ
    rw [e1]; exact hresZ l
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l) := by
    intro Q hQ
    rw [hdom] at hQ
    exact Place.ord_nonneg_of_mem' Q (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e Q hQ l hl).1
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hx : (nodeTgt Γ e).IsRational := nodeTgt_isRational' Γ e
  have hmod0' : ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) := by
    rw [mul_comm (Δ.annIn e).param, hmod]; exact htwo
  have hR' : R ∈ (Δ.annOut e).dom := by rw [hdom]; exact hR
  have hout' : ∀ Q ∈ (Δ.annOut e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
      μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param) := by
    intro Q hQ; rw [hdom] at hQ; exact hout Q hQ
  exact AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' (chart Γ (tgt p e)) (nodeTgt Γ e) hattOut hx
    (chart Γ (src p e)) (nodeSrc Γ e) hattIn hwide (goodFamily Φ l) hint hres c' hc'0 hc'A hC' hres' hpole hzoC R hR' hout'

end TubeSepTangent

end ModularCurve.MultCovering

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.ModularCurve.MultCovering"

theorem solution (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e : Fin (mAnnuli p)) (l₁ l₂ : Fin r) (hl₁ : 1 ≤ (l₁ : ℕ)) (hl₂ : 1 ≤ (l₂ : ℕ))
    (hint₁ : goodFamily Φ l₁ ∈ (infChart Γ).integers)
    (hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint₁⟩) = 1)
    (hint₂ : goodFamily Φ l₂ ∈ (infChart Γ).integers)
    (hord₂ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hint₂⟩) = 1)
    (hint0₁ : goodFamilyZero Φ.toFamData l₁ ∈ (zeroChart Γ).integers)
    (hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩) = 0)
    (hint0₂ : goodFamilyZero Φ.toFamData l₂ ∈ (zeroChart Γ).integers)
    (hβ₂ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint0₂⟩) ≤ 0)
    (hn : hasseExp Φ.toFamData l₁ < hasseExp Φ.toFamData l₂)
    (hsep : ∀ Q ∈ (zeroChart Γ).dom,
      ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩)
        ≠ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (∃ i' j', evalVec s R i' * evalVec s Q j' ≠ evalVec s R j' * evalVec s Q i') →
        |prox μ (evalVec s R) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  intro μ hμ hμA R hR Q hQ hnonprop
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : (AlgebraicClosure ℚ)) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hμp0 : 0 < μ (p : (AlgebraicClosure ℚ)) := μ.pos hp0
  have hμp1' : μ (p : (AlgebraicClosure ℚ)) ≤ 1 := (hμA _).1 hpA

  have hμp1 : μ (p : (AlgebraicClosure ℚ)) < 1 := by
    have hπ : (((Δ.annIn e).modulus : ↥A) : (AlgebraicClosure ℚ)) = (p : (AlgebraicClosure ℚ)) ^ jWidth (ssValue Γ e) := by
      show (((Δ.An e).modulus : ↥A) : (AlgebraicClosure ℚ)) = _
      rw [Δ.modulus_eq e]; norm_cast
    have hm := (Δ.annIn e).modulus_mem
    have hlt : μ ((p : (AlgebraicClosure ℚ)) ^ jWidth (ssValue Γ e)) < 1 := by
      rw [← hπ]; exact abv_lt_one_of_mem_maximalIdeal_vs μ hμA ((Δ.annIn e).modulus).2 (by simpa using hm)
    rw [map_pow] at hlt
    by_contra hge; push_neg at hge
    exact absurd hlt (not_lt.2 (one_le_pow₀ hge))
  have hr0 : 0 < r := Fin.pos l₁
  set o : Fin r := ⟨0, hr0⟩ with ho

  obtain ⟨hQrat, hC1⟩ := abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom p A hA Γ Φ μ hμA Q hQ
  obtain ⟨hRrat, -, -, -, -⟩ := (Δ.annIn e).mem_dom R hR
  obtain ⟨-, hzoR, -, hzoR0, -⟩ := (Δ.annOut e).mem_dom R (by rw [hdom]; exact hR)
  have hsmallR : ∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ l)) < 1 :=
    fun l hl => abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e R hR l hl
  set t := goodFamily Φ with ht
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have ht0 : ∀ i, t i ≠ 0 := fun i => Φ.t_basis.1.ne_zero i
  have hto : t o = 1 := goodFamily_zero_eq_one p Φ o rfl
  set zR : (AlgebraicClosure ℚ) := R.evalAt (Δ.annOut e).param with hzR_def
  have htR : ∀ i, t i ∈ R.toValuationSubring := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmallR i hi).1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto]; exact one_mem _
  have htQ : ∀ i, t i ∈ Q.toValuationSubring := fun i => (hC1 i).1
  set x : Fin r → (AlgebraicClosure ℚ) := fun i => R.evalAt (t i * (t o)⁻¹) with hx
  set y : Fin r → (AlgebraicClosure ℚ) := fun i => Q.evalAt (t i * (t o)⁻¹) with hy
  have hxeval : ∀ i, x i = R.evalAt (t i) := fun i => by simp [hx, hto]
  have hyeval : ∀ i, y i = Q.evalAt (t i) := fun i => by simp [hy, hto]
  have hxo : x o = 1 := by rw [hxeval, hto, Place.evalAt_one]
  have hyo : y o = 1 := by rw [hyeval, hto, Place.evalAt_one]
  have hxle : ∀ i, μ (x i) ≤ 1 := by
    intro i; rw [hxeval]
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmallR i hi).2.le
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto, Place.evalAt_one, map_one]
  have hyn : ∀ i, μ (y i) ≤ μ (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData i := fun i => by rw [hyeval]; exact (hC1 i).2
  have hyle : ∀ i, μ (y i) ≤ 1 := fun i => (hyn i).trans (pow_le_one₀ hμp0.le hμp1')

  have hcore : ∃ l : Fin r, μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp < μ (x l - y l) := by
    by_cases hbig : ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ μ ((p : (AlgebraicClosure ℚ))) ^ hasseExp Φ.toFamData l < μ (x l)
    ·
      obtain ⟨l, hl1, hlt⟩ := hbig
      refine ⟨l, ?_⟩
      have hylt : μ (y l) < μ (x l) := lt_of_le_of_lt (hyn l) hlt
      rw [abv_sub_eq_of_abv_lt μ hμ hylt]
      refine lt_of_le_of_lt ?_ hlt
      exact pow_le_pow_of_le_one hμp0.le hμp1' (hasseExp_le_modulusExp p A hA Γ Δ Φ l)
    ·
      push_neg at hbig
      have hsat : ∀ l : Fin r, 1 ≤ (l : ℕ) → μ (R.evalAt (goodFamily Φ l)) ≤ μ ((p : (AlgebraicClosure ℚ))) ^ hasseExp Φ.toFamData l :=
        fun l hl => by rw [← hxeval]; exact hbig l hl

      have hnotfree : ∀ (l : Fin r) (hl : 1 ≤ (l : ℕ)) (hintl : goodFamily Φ l ∈ (infChart Γ).integers)
          (hordl : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintl⟩) = 1),
          ¬ (∀ P ∈ (Δ.annIn e).dom, P.ord (goodFamily Φ l) = 0) := by
        intro l hl hintl hordl hzf
        obtain ⟨hmodeq, -, hprof⟩ := abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
          p A hA Γ Δ Φ e l hintl hordl hzf μ hμA
        obtain ⟨-, -, heq, hlt⟩ := hprof R hR
        have := hsat l hl
        rw [heq, hmodeq] at this
        exact absurd hlt (not_lt.2 this)

      have hreg₂ : ∀ P ∈ (Δ.annIn e).dom, goodFamily Φ l₂ ∈ P.toValuationSubring := fun P hP =>
        (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e P hP l₂ hl₂).1
      have hreg₁ : ∀ P ∈ (Δ.annIn e).dom, goodFamily Φ l₁ ∈ P.toValuationSubring := fun P hP =>
        (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e P hP l₁ hl₁).1
      obtain hzf₂ | ⟨Q₂, hQ₂, huniq₂, hQ₂pos, hdepth₂⟩ :=
        zeroFree_or_exists_unique_zero_of_ord_one_of_ord_zeroChart_le_zero p A hA Γ Δ Φ e μ hμA l₂ hint₂ hord₂ hint0₂ hβ₂ hreg₂
      · exact absurd hzf₂ (hnotfree l₂ hl₂ hint₂ hord₂)
      obtain hzf₁ | ⟨Q₁, hQ₁, huniq₁, hQ₁pos, hdepth₁⟩ :=
        zeroFree_or_exists_unique_zero_of_ord_one_of_ord_zeroChart_le_zero p A hA Γ Δ Φ e μ hμA l₁ hint₁ hord₁ hint0₁ hβ₁.le hreg₁
      · exact absurd hzf₁ (hnotfree l₁ hl₁ hint₁ hord₁)

      have hRdepth : μ zR ≤ μ (Q₂.evalAt (Δ.annOut e).param) := by
        by_contra hlt; push_neg at hlt
        have hout : ∀ P ∈ (Δ.annIn e).dom, P.ord (goodFamily Φ l₂) ≠ 0 →
            μ (P.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param) := by
          intro P hP hne; rw [huniq₂ P hP hne]; exact hlt
        have hattOut' := Δ.attached_tgt e
        obtain ⟨-, hzoC, hzoord, -⟩ := hattOut'
        obtain ⟨hmem, hunit, -⟩ := tubeMember_value_D p A hA Γ Δ Φ e μ hμ hμA R hR l₂ hl₂ hout hint₂ hzoC
        have ha : (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l₂, hint₂⟩) = 1 := hord₂
        have e1 : R.evalAt (goodFamily Φ l₂) * (R.evalAt (Δ.annOut e).param) ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l₂, hint₂⟩)))
            = R.evalAt (goodFamily Φ l₂) * zR⁻¹ := by rw [ha, zpow_neg_one]
        have hmem' : R.evalAt (goodFamily Φ l₂) * zR⁻¹ ∈ A := e1 ▸ hmem
        have hunit' : IsUnit (⟨_, hmem'⟩ : ↥A) := by
          have : (⟨_, hmem⟩ : ↥A) = ⟨_, hmem'⟩ := Subtype.ext e1
          rw [← this]; exact hunit
        have h1 : μ (R.evalAt (goodFamily Φ l₂) * zR⁻¹) = 1 := abv_eq_one_of_isUnit_vs μ hμA hmem' hunit'
        rw [map_mul, map_inv₀] at h1
        have hx2 : μ (R.evalAt (goodFamily Φ l₂)) = μ zR := by
          have hz : μ zR ≠ 0 := (μ.pos hzoR0).ne'
          field_simp at h1; linarith
        have := hsat l₂ hl₂
        rw [hx2, ← hdepth₂] at this
        exact absurd hlt (not_lt.2 this)
      have hRbelow : μ zR < μ (Q₁.evalAt (Δ.annOut e).param) := by
        rw [hdepth₁]
        refine lt_of_le_of_lt (hRdepth.trans_eq hdepth₂) ?_
        exact pow_lt_pow_right_of_lt_one₀ hμp0 hμp1 hn

      obtain ⟨hA1, hU1, hres1⟩ := isUnit_evalAt_goodFamilyZero_of_abv_lt p A hA Γ Δ Φ e μ hμ hμA l₁ hl₁ hint₁ hint0₁ hβ₁
        Q₁ hQ₁ huniq₁ hQ₁pos R hR hRbelow

      set tZ := goodFamilyZero Φ.toFamData l₁ with htZ
      have etZ : tZ = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l₁))⁻¹ * goodFamily Φ l₁ := rfl
      have hpn0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l₁) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp0)
      have htZreg : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), goodFamily Φ l₁ ∈ P.toValuationSubring → tZ ∈ P.toValuationSubring := by
        intro P hP; rw [etZ, ← map_inv₀]; exact mul_mem (P.algebraMap_mem' _) hP
      have htZQ : tZ ∈ Q.toValuationSubring := htZreg Q (htQ l₁)
      have htZval : ∀ (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))), P.IsRational → goodFamily Φ l₁ ∈ P.toValuationSubring →
          P.evalAt tZ = ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l₁)⁻¹ * P.evalAt (goodFamily Φ l₁) := by
        intro P hPrat hP
        rw [etZ, ← map_inv₀, Place.evalAt_mul' P hPrat (P.algebraMap_mem' _) hP, Place.evalAt_algebraMap']
      have hyA : Q.evalAt tZ ∈ A := by
        rw [htZval Q hQrat (htQ l₁)]
        refine (hμA _).2 ?_
        rw [map_mul, map_inv₀, map_pow]
        have := (hC1 l₁).2
        have hpn : 0 < μ (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l₁ := pow_pos hμp0 _
        exact (inv_mul_le_iff₀ hpn).2 (by rw [mul_one]; exact this)

      have hfib : ∀ w ∈ (zeroChart Γ).dom, (zeroChart Γ).placeMap w = (zeroChart Γ).placeMap Q → tZ ∈ w.toValuationSubring := by
        intro w hw _
        exact htZreg w ((abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom p A hA Γ Φ μ hμA w hw).2 l₁).1
      obtain ⟨hm, hyA', hcomp⟩ := (zeroChart Γ).pointwise Q hQ hQrat tZ hint0₁ hfib
      have hQbar : ((zeroChart Γ).placeMap Q).IsRational := isRational_Fbar (p := p) 1 _
      have hresQ : IsLocalRing.residue ↥A ⟨Q.evalAt tZ, hyA⟩
          = ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨tZ, hint0₁⟩) := by
        have e1 : (⟨Q.evalAt tZ, hyA⟩ : ↥A) = ⟨Q.evalAt tZ, hyA'⟩ := rfl
        apply ((zeroChart Γ).placeMap Q).algebraMap_residueField_injective
        rw [hcomp, ← ((zeroChart Γ).placeMap Q).algebraMap_evalAt hQbar hm]

      have hdiff : IsLocalRing.residue ↥A (⟨R.evalAt tZ, hA1⟩ - ⟨Q.evalAt tZ, hyA⟩) ≠ 0 := by
        rw [map_sub, hres1, hresQ, sub_ne_zero]
        exact (hsep Q hQ).symm
      have hdu : IsUnit ((⟨R.evalAt tZ, hA1⟩ : ↥A) - ⟨Q.evalAt tZ, hyA⟩) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hdiff
      have hd1 : μ (R.evalAt tZ - Q.evalAt tZ) = 1 := by
        have := abv_eq_one_of_isUnit_vs μ hμA (sub_mem hA1 hyA) (by exact hdu)
        exact this

      refine ⟨l₁, ?_⟩
      have hxy : x l₁ - y l₁ = (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l₁ * (R.evalAt tZ - Q.evalAt tZ) := by
        rw [hxeval, hyeval, htZval R hRrat (htR l₁), htZval Q hQrat (htQ l₁)]
        field_simp
        rfl
      rw [hxy, map_mul, hd1, mul_one, map_pow]
      have hn2 : hasseExp Φ.toFamData l₁ < modulusExp :=
        lt_of_lt_of_le hn (hasseExp_le_modulusExp p A hA Γ Δ Φ l₂)
      exact pow_lt_pow_right_of_lt_one₀ hμp0 hμp1 hn2

  obtain ⟨lc, hlc⟩ := hcore
  set M := linkMatrix Φ s hs with hM
  set Minv := linkMatrixInv Φ s hs with hMinv
  set B := linkBudget Φ s hs with hB
  obtain ⟨dP, hdP0, hdP⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr0 s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    R hRrat o (fun j => by rw [hto, inv_one, mul_one]; exact htR j)
  obtain ⟨dQ, hdQ0, hdQ⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr0 s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    Q hQrat o (fun j => by rw [hto, inv_one, mul_one]; exact htQ j)
  obtain ⟨i', j', hij⟩ := hnonprop
  have hminor : ∀ i j, evalVec s R i * evalVec s Q j - evalVec s R j * evalVec s Q i
      = dP * dQ * (M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i) := by
    intro i j; rw [hdP, hdQ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hMm : M.mulVec x i' * M.mulVec y j' - M.mulVec x j' * M.mulVec y i' ≠ 0 := by
    intro h0; apply hij; exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsupM : (⨆ q : Fin r × Fin r, μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1)) ≠ 0 :=
    ((μ.pos hMm).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1))) (i', j'))).ne'
  have hrowminor : ∃ i j, x i * y j - x j * y i ≠ 0 := by
    by_contra hall; push_neg at hall; apply hMm
    rw [minor_mulVec_D]; exact Finset.sum_eq_zero fun q _ => by rw [hall q.1 q.2, mul_zero]
  obtain ⟨i1, j1, hm1⟩ := hrowminor
  have hx0 : x ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hxo] at this; exact one_ne_zero this
  have hy0 : y ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hyo] at this; exact one_ne_zero this
  set β : ℝ := (μ (p : (AlgebraicClosure ℚ)))⁻¹ ^ B with hβ
  have hμp0 : 0 < μ (p : (AlgebraicClosure ℚ)) := μ.pos hp0
  have hμp1 : μ (p : (AlgebraicClosure ℚ)) ≤ 1 := (hμA _).1 hpA
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1)
  have hlogβ : Real.log β = (B : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
    rw [hβ, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : (AlgebraicClosure ℚ), (p : (AlgebraicClosure ℚ)) ^ B * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : (AlgebraicClosure ℚ)) ^ B * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : (AlgebraicClosure ℚ)) ^ B := pow_pos hμp0 _
    rw [hβ, inv_pow]
    calc μ m = (μ (p : (AlgebraicClosure ℚ)) ^ B * μ m) * (μ (p : (AlgebraicClosure ℚ)) ^ B)⁻¹ := by field_simp
      _ ≤ 1 * (μ (p : (AlgebraicClosure ℚ)) ^ B)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : (AlgebraicClosure ℚ)) ^ B)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).1
  have hMβ' : ∀ i j, μ (Minv i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).2
  have hprox1 : prox μ (evalVec s R) (evalVec s Q) = prox μ (M.mulVec x) (M.mulVec y) := by
    rw [hdP, hdQ]; exact AlgebraicCurve.prox_smul_smul μ _ _ hdP0 hdQ0 hsupM
  have hL := AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M Minv (linkMatrixInv_mul Φ s hs)
    β hβ1 hMβ hMβ' x y hx0 hy0 ⟨i1, j1, hm1⟩
  rw [hlogβ, ← hprox1] at hL
  have hpxy := AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ x y o hxo hyo hxle hyle
  set S : ℝ := ⨆ i, μ (x i - y i) with hS
  have hSbdd := Finite.bddAbove_range (fun i : Fin r => μ (x i - y i))
  have hSge : μ (x lc - y lc) ≤ S := le_ciSup hSbdd lc
  have hSpos : 0 < S := lt_of_lt_of_le (lt_trans (pow_pos hμp0 _) hlc) hSge
  have hSle : S ≤ 1 := by
    haveI : Nonempty (Fin r) := ⟨o⟩
    refine ciSup_le fun i => ?_
    exact (abv_sub_le_max μ hμA _ _).trans (max_le (hxle i) (hyle i))
  have hpxy0 : 0 ≤ prox μ x y := by
    rw [hpxy]; exact neg_nonneg.2 (Real.log_nonpos hSpos.le hSle)
  have hpxy3 : prox μ x y ≤ (modulusExp : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
    rw [hpxy]
    have h1 : μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp < S := lt_of_lt_of_le hlc hSge
    have h2 := Real.log_lt_log (pow_pos hμp0 _) h1
    rw [Real.log_pow] at h2
    show -Real.log S ≤ _
    linarith
  have hlam : 0 ≤ -Real.log (μ (p : (AlgebraicClosure ℚ))) := by linarith [Real.log_nonpos hμp0.le hμp1]
  calc |prox μ (evalVec s R) (evalVec s Q)|
      = |(prox μ (evalVec s R) (evalVec s Q) - prox μ x y) + prox μ x y| := by ring_nf
    _ ≤ |prox μ (evalVec s R) (evalVec s Q) - prox μ x y| + |prox μ x y| := abs_add_le _ _
    _ ≤ 4 * ((B : ℝ) * -Real.log (μ (p : (AlgebraicClosure ℚ)))) + (modulusExp : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
        refine add_le_add hL ?_
        rw [abs_of_nonneg hpxy0]; exact hpxy3
    _ ≤ compConst Φ s hs * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
        rw [compConst_eq, hB]
        have hme : (0 : ℝ) ≤ modulusExp := by positivity
        nlinarith

end S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers (solution)
