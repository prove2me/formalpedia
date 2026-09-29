-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_annIn_of_leadingTerms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/629a07c8-51dd-5386-99a8-8cdcea419bc7

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve"

open AlgebraicCurve IsLocalRing

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

theorem chart_isUnit_of_residue_ne_zero_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

theorem vs_inv_mem_of_isUnit_D {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
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

theorem chart_residue_inv_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

theorem ord_eq_zero_of_evalAt_ne_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h' | h'
    · simp [h']
    · exact h'
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
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

theorem abv_lt_one_of_mem_maximalIdeal_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {m : ↥A} (hm : m ∈ IsLocalRing.maximalIdeal ↥A) : μ (m : AlgebraicClosure ℚ) < 1 := by
  have hle : μ (m : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 m.2
  refine lt_of_le_of_ne hle fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have hm0 : (m : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hinv : (m : AlgebraicClosure ℚ)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0)⟩

theorem isRational_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (h : v.deg = 1) :
    v.IsRational := by
  intro x
  have h1 : Module.finrank K v.ResidueField = 1 := h
  have htop : (⊥ : Subalgebra K v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by rw [htop]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

theorem isRational_modularFunctionFieldBar {p : ℕ} [Fact p.Prime] (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    v.IsRational :=
  isRational_of_deg_eq_one v (ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * p) v)

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

section MoreHelpers

theorem evalAt_sub_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_add_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem mem_maximalIdeal_of_abv_lt_one_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : μ x < 1) : (⟨x, hx⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have hinv : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x⁻¹ := by
    have h1 := congrArg (fun t : ↥A => (t : AlgebraicClosure ℚ)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxinv : μ x⁻¹ ≤ 1 := (hμA _).1 (hinv ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2)
  rw [map_inv₀] at hxinv
  have : 1 < (μ x)⁻¹ := (one_lt_inv₀ (μ.pos hx0)).2 h
  linarith

theorem chart_residue_algebraMap_eq_zero_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

end MoreHelpers

section FamilyFacts
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)

theorem goodFamily_ne_zero' (i : Fin r) : goodFamily Φ i ≠ 0 := Φ.t_basis.1.ne_zero i

theorem goodFamily_mem_riemannRochSpace' (i : Fin r) : goodFamily Φ i ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← Φ.t_basis.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem goodFamilyZero_eq_inv_mul' (l : Fin r) :
    goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * goodFamily Φ l := rfl

theorem goodFamily_mem_of_ne_cuspInftyBar'
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : w ≠ cuspInftyBar (1 * p)) (i : Fin r) :
    0 ≤ w.ord (goodFamily Φ i) ∧ goodFamily Φ i ∈ w.toValuationSubring := by
  have h0 : goodFamily Φ i ≠ 0 := goodFamily_ne_zero' Φ i
  have hmem := (mem_riemannRochSpace_iff.mp (goodFamily_mem_riemannRochSpace' Φ i)) w
  have hD : (embDivisor (1 * p)) w = 0 := by simp [embDivisor, hw]
  rcases hmem with h' | h'
  · exact absurd h' h0
  · rw [hD, neg_zero] at h'
    exact ⟨h', w.mem_of_ord_nonneg h0 h'⟩

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

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

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

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve"

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem cross_of_untied_D (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (R Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hRrat : R.IsRational) (hQrat : Q.IsRational)
    (hR : ∀ i, goodFamily Φ i ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ i)) ≤ 1)
    (hQ : ∀ i, goodFamily Φ i ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ i)) ≤ 1)
    (l : Fin r) (hne : R.evalAt (goodFamily Φ l) ≠ Q.evalAt (goodFamily Φ l))
    (hbig : -Real.log (μ (R.evalAt (goodFamily Φ l) - Q.evalAt (goodFamily Φ l))) ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))))
    (hnonprop : ∃ i' j', evalVec s R i' * evalVec s Q j' ≠ evalVec s R j' * evalVec s Q i') :
    |prox μ (evalVec s R) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  obtain ⟨i', j', hij⟩ := hnonprop
  have hr : 0 < r := Fin.pos l
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have ht0 : ∀ i, goodFamily Φ i ≠ 0 := goodFamily_ne_zero' Φ
  set t := goodFamily Φ with ht
  set M := linkMatrix Φ s hs with hM
  set Minv := linkMatrixInv Φ s hs with hMinv
  set B := linkBudget Φ s hs with hB
  set o : Fin r := ⟨0, hr⟩ with ho
  have hto : t o = 1 := goodFamily_zero_eq_one p Φ o rfl

  set x : Fin r → AlgebraicClosure ℚ := fun i => R.evalAt (t i * (t o)⁻¹) with hx
  set y : Fin r → AlgebraicClosure ℚ := fun i => Q.evalAt (t i * (t o)⁻¹) with hy
  have hxeval : ∀ i, x i = R.evalAt (t i) := fun i => by simp [hx, hto]
  have hyeval : ∀ i, y i = Q.evalAt (t i) := fun i => by simp [hy, hto]
  have hxo : x o = 1 := by rw [hxeval, hto, Place.evalAt_one]
  have hyo : y o = 1 := by rw [hyeval, hto, Place.evalAt_one]
  have hxle : ∀ i, μ (x i) ≤ 1 := fun i => by rw [hxeval]; exact (hR i).2
  have hyle : ∀ i, μ (y i) ≤ 1 := fun i => by rw [hyeval]; exact (hQ i).2
  have hne' : x l ≠ y l := by rw [hxeval, hyeval]; exact hne
  have hdl0 : 0 < μ (x l - y l) := μ.pos (sub_ne_zero.2 hne')
  have hbig' : -Real.log (μ (x l - y l)) ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by rw [hxeval, hyeval]; exact hbig

  obtain ⟨dP, hdP0, hdP⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    R hRrat o (fun j => by rw [hto, inv_one, mul_one]; exact (hR j).1)
  obtain ⟨dQ, hdQ0, hdQ⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    Q hQrat o (fun j => by rw [hto, inv_one, mul_one]; exact (hQ j).1)

  have hminor : ∀ i j, evalVec s R i * evalVec s Q j - evalVec s R j * evalVec s Q i
      = dP * dQ * (M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i) := by
    intro i j; rw [hdP, hdQ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hMm : M.mulVec x i' * M.mulVec y j' - M.mulVec x j' * M.mulVec y i' ≠ 0 := by
    intro h0; apply hij; exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsupM : (⨆ q : Fin r × Fin r, μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1)) ≠ 0 :=
    ((μ.pos hMm).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1))) (i', j'))).ne'

  have hsub : ∀ a b : AlgebraicClosure ℚ, μ (a - b) ≤ max (μ a) (μ b) := by
    intro a b; rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ b]; exact hμ _ _
  have hm1 : x o * y l - x l * y o ≠ 0 := by
    rw [hxo, hyo, one_mul, mul_one]
    intro h0
    exact hne' (sub_eq_zero.1 h0).symm
  have hx0 : x ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hxo] at this; exact one_ne_zero this
  have hy0 : y ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hyo] at this; exact one_ne_zero this

  set β : ℝ := (μ (p : AlgebraicClosure ℚ))⁻¹ ^ B with hβ
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 hpA
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1)
  have hlogβ : Real.log β = (B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    rw [hβ, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : AlgebraicClosure ℚ, (p : AlgebraicClosure ℚ) ^ B * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : AlgebraicClosure ℚ) ^ B * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : AlgebraicClosure ℚ) ^ B := pow_pos hμp0 _
    rw [hβ, inv_pow]
    calc μ m = (μ (p : AlgebraicClosure ℚ) ^ B * μ m) * (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := by field_simp
      _ ≤ 1 * (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).1
  have hMβ' : ∀ i j, μ (Minv i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).2

  have hprox1 : prox μ (evalVec s R) (evalVec s Q) = prox μ (M.mulVec x) (M.mulVec y) := by
    rw [hdP, hdQ]; exact AlgebraicCurve.prox_smul_smul μ _ _ hdP0 hdQ0 hsupM
  have hL := AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M Minv (linkMatrixInv_mul Φ s hs)
    β hβ1 hMβ hMβ' x y hx0 hy0 ⟨o, l, hm1⟩
  rw [hlogβ, ← hprox1] at hL

  have hS := AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ x y o hxo hyo hxle hyle
  have hS_le : (⨆ i, μ (x i - y i)) ≤ 1 := by
    haveI : Nonempty (Fin r) := ⟨o⟩
    exact ciSup_le fun i => (hsub _ _).trans (max_le (hxle i) (hyle i))
  have hS_ge : μ (x l - y l) ≤ ⨆ i, μ (x i - y i) :=
    le_ciSup (Finite.bddAbove_range fun i => μ (x i - y i)) l
  have hS0 : 0 < ⨆ i, μ (x i - y i) := lt_of_lt_of_le hdl0 hS_ge
  have hprox_nonneg : 0 ≤ prox μ x y := by
    rw [hS]; exact neg_nonneg.mpr (Real.log_nonpos hS0.le hS_le)
  have hprox_le : prox μ x y ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    rw [hS]
    exact (neg_le_neg (Real.log_le_log hdl0 hS_ge)).trans hbig'

  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) := by linarith [Real.log_nonpos hμp0.le hμp1]
  have habs : |prox μ (evalVec s R) (evalVec s Q)| ≤
      4 * ((B : ℝ) * -Real.log (μ (p : AlgebraicClosure ℚ))) + 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    have h1 : |prox μ (evalVec s R) (evalVec s Q)| ≤
        |prox μ (evalVec s R) (evalVec s Q) - prox μ x y| + |prox μ x y| := by
      have := abs_add_le (prox μ (evalVec s R) (evalVec s Q) - prox μ x y) (prox μ x y)
      rwa [sub_add_cancel] at this
    have h2 : |prox μ x y| ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
      rw [abs_of_nonneg hprox_nonneg]; exact hprox_le
    linarith
  have hbudget : 4 * (B : ℝ) + 3 ≤ compConst Φ s hs := by
    rw [compConst_eq, hB, show (modulusExp : ℝ) = 3 by norm_num [modulusExp]]; linarith
  calc |prox μ (evalVec s R) (evalVec s Q)|
      ≤ 4 * ((B : ℝ) * -Real.log (μ (p : AlgebraicClosure ℚ))) + 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := habs
    _ = (4 * (B : ℝ) + 3) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by ring
    _ ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := mul_le_mul_of_nonneg_right hbudget hlam

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

section P2Helpers

theorem abv_sub_eq_max_of_ne_D {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {a b : K} (h : μ a ≠ μ b) : μ (a - b) = max (μ a) (μ b) := by
  have hsub : ∀ u v : K, μ (u - v) ≤ max (μ u) (μ v) := by
    intro u v; rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ v]; exact hμ _ _
  refine le_antisymm (hsub a b) ?_
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [max_eq_right hlt.le]
    have h1 := hμ (b - a) a
    rw [sub_add_cancel] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · rw [← neg_sub, AbsoluteValue.map_neg] at h2; exact h2
    · exact absurd h2 (not_le.2 hlt)
  · rw [max_eq_left hlt.le]
    have h1 := hμ (a - b) b
    rw [sub_add_cancel] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 hlt)

theorem abv_sub_le_max_D {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (a b : K) : μ (a - b) ≤ max (μ a) (μ b) := by
  rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ b]; exact hμ _ _

theorem abv_eq_one_of_isUnit_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (hu : IsUnit (⟨x, hx⟩ : ↥A)) : μ x = 1 := by
  refine le_antisymm ((hμA x).1 hx) ?_
  have hinv : x⁻¹ ∈ A := vs_inv_mem_of_isUnit_D hx hu
  have hx0 : x ≠ 0 := by
    intro h0; obtain ⟨u, hu'⟩ := hu
    have : (u : ↥A) = 0 := by rw [hu']; exact Subtype.ext h0
    exact u.ne_zero this
  have h1 : μ x⁻¹ ≤ 1 := (hμA _).1 hinv
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (μ.pos hx0)).1 h1

theorem isUnit_of_abv_eq_one_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : μ x = 1) : IsUnit (⟨x, hx⟩ : ↥A) := by
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hinv : x⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem abv_lt_one_of_residue_eq_zero_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : IsLocalRing.residue ↥A ⟨x, hx⟩ = 0) : μ x < 1 :=
  abv_lt_one_of_mem_maximalIdeal_D μ hμA ((IsLocalRing.residue_eq_zero_iff _).1 h)

theorem evalAt_eq_zero_of_ord_ne_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (h : v.ord f ≠ 0) : v.evalAt f = 0 := by
  by_contra hne
  exact h (ord_eq_zero_of_evalAt_ne_zero_D v hf hne)

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

theorem nodeTgt_isRational_D (Γ : ChartCtx p A) (ε : Fin (mAnnuli p)) : (nodeTgt Γ ε).IsRational := by
  apply isRational_of_deg_eq_one
  exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ ε)

theorem nodeSrc_isRational_D (Γ : ChartCtx p A) (ε : Fin (mAnnuli p)) : (nodeSrc Γ ε).IsRational := by
  apply isRational_of_deg_eq_one
  exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ ε ^ p)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem engine_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hβ : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ Q ∈ (Δ.annIn ε).dom,
      μ (Q.evalAt (Δ.annOut ε).param) = μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l ∧
      (∀ X ∈ (Δ.annIn ε).dom, X.ord (goodFamily Φ l) ≠ 0 → X = Q) ∧
      (∃ hq : Q.evalAt (Δ.annOut ε).param * ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l)⁻¹ ∈ A,
        IsUnit (⟨_, hq⟩ : ↥A) ∧
        IsLocalRing.residue ↥A ⟨_, hq⟩
          = -((nodeSrc Γ ε).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩))
              * ((nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
                  * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹))⁻¹) ∧
      ∀ X ∈ (Δ.annIn ε).dom,
        ∃ hu : X.evalAt (goodFamily Φ l * ((Δ.annOut ε).param
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹) ∈ A,
          IsUnit (⟨_, hu⟩ : ↥A) ∧
          IsLocalRing.residue ↥A ⟨_, hu⟩
            = (nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
                * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹) ∧
          X.evalAt (goodFamily Φ l)
            = X.evalAt (goodFamily Φ l * ((Δ.annOut ε).param
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹)
              * (X.evalAt (Δ.annOut ε).param - Q.evalAt (Δ.annOut ε).param) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set n := hasseExp Φ.toFamData l with hn
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ n with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
  set zo := (Δ.annOut ε).param with hzo
  have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
  have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
    intro h0
    have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  have hscaled : goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hint0
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
  have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint0⟩ := Subtype.ext hscaled.symm
  have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
  have hord't : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨_, hC't⟩) = 0 := by rw [e2]; exact hβ
  have hrow : ∀ X ∈ (Δ.annIn ε).dom, t l ∈ X.toValuationSubring :=
    fun X hX => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε X hX l hl).1
  have hpole : ∀ X ∈ (Δ.annOut ε).dom, 0 ≤ X.ord (t l) := fun X hX => X.ord_nonneg_of_mem (hrow X (hdom ▸ hX))
  obtain ⟨Q, hQdom, hordQ, hordP, hμQ, ⟨hq, hqunit, hqres⟩, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one μ hμA
      (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
      (nodeTgt_isRational_D Γ ε) (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε) (nodeSrc_isRational_D Γ ε)
      hwide (t l) hint hrest hord c₁ hc₁0 hc₁A hC't hres't hord't hpole hz
  refine ⟨Q, hdom ▸ hQdom, by rw [hμQ, hc₁, map_pow], ?_, ⟨hq, hqunit, ?_⟩, ?_⟩
  · intro X hX hXord
    by_contra hXQ
    exact hXord (hordP X (hdom ▸ hX) hXQ)
  · rw [hqres, e2]
  · intro X hX
    have hXout : X ∈ (Δ.annOut ε).dom := hdom ▸ hX
    obtain ⟨hu, huunit, hures⟩ := hfac X hXout
    refine ⟨hu, huunit, hures, ?_⟩
    obtain ⟨hXrat, hzoX, -, hzoX0, -⟩ := (Δ.annOut ε).mem_dom X hXout
    have htX : t l ∈ X.toValuationSubring := hrow X hX
    by_cases hXQ : X = Q
    · subst hXQ
      have hev : X.evalAt (t l) = 0 := evalAt_eq_zero_of_ord_ne_zero_D X htX (by rw [hordQ]; exact one_ne_zero)
      rw [hev, sub_self, mul_zero]
    · have hwX : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param) ∈ X.toValuationSubring :=
        sub_mem hzoX (X.algebraMap_mem' _)
      have hwev : X.evalAt (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param)) = X.evalAt zo - Q.evalAt (Δ.annOut ε).param := by
        rw [evalAt_sub_D X hXrat hzoX (X.algebraMap_mem' _), evalAt_algebraMap_D]
      have hwne : X.evalAt zo - Q.evalAt (Δ.annOut ε).param ≠ 0 := by
        rw [sub_ne_zero]
        intro h1; apply hXQ
        obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := (Δ.annOut ε).mem_dom Q hQdom
        obtain ⟨P₀, -, huniq⟩ := (Δ.annOut ε).existsUnique_evalAt_eq ⟨Q.evalAt (Δ.annOut ε).param, haA⟩ ha𝔪 ha0 hm
        exact (huniq X ⟨hXout, h1⟩).trans (huniq Q ⟨hQdom, rfl⟩).symm
      have hev0 : X.evalAt (0 : modularFunctionFieldBar (1 * p)) = 0 := by
        rw [X.evalAt_of_mem (zero_mem _)]
        have : (⟨(0 : modularFunctionFieldBar (1 * p)), zero_mem _⟩ : X.toValuationSubring) = 0 := rfl
        rw [this, map_zero, ← map_zero (algebraMap (AlgebraicClosure ℚ) X.ResidueField), X.residueInv_algebraMap]
      have hw0 : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param) ≠ 0 := by
        intro h0; apply hwne; rw [← hwev, h0, hev0]
      have hordw : X.ord (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param)) = 0 :=
        ord_eq_zero_of_evalAt_ne_zero_D X hwX (by rw [hwev]; exact hwne)
      have hwinvX : (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹ ∈ X.toValuationSubring :=
        X.mem_of_ord_nonneg (inv_ne_zero hw0) (by rw [Place.ord_inv, hordw]; norm_num)
      rw [← hwev, ← evalAt_mul_D X hXrat (mul_mem htX hwinvX) hwX, inv_mul_cancel_right₀ hw0]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem outerUnit_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (X : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hX : X ∈ (Δ.annIn ε).dom)
    (hout : ∀ Y ∈ (Δ.annIn ε).dom, Y.ord (goodFamily Φ l) ≠ 0 →
      μ (Y.evalAt (Δ.annOut ε).param) < μ (X.evalAt (Δ.annOut ε).param)) :
    ∃ hmem : X.evalAt (goodFamily Φ l) * (X.evalAt (Δ.annOut ε).param)⁻¹ ∈ A,
      IsUnit (⟨_, hmem⟩ : ↥A) ∧
      IsLocalRing.residue ↥A ⟨_, hmem⟩
        = (nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
            * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
  set zo := (Δ.annOut ε).param with hzo
  have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
  have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
    intro h0
    have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  have hscaled : goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hint0
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
  have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
  have hrow : ∀ Y ∈ (Δ.annIn ε).dom, t l ∈ Y.toValuationSubring :=
    fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Y hY l hl).1
  have hpole : ∀ Y ∈ (Δ.annOut ε).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
  have hout' : ∀ Y ∈ (Δ.annOut ε).dom, Y.ord (t l) ≠ 0 → μ (Y.evalAt zo) < μ (X.evalAt zo) :=
    fun Y hY hYord => hout Y (hdom ▸ hY) hYord
  obtain ⟨hmem, hunit, hres⟩ :=
    AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt μ hμA
      (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
      (nodeTgt_isRational_D Γ ε) (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε)
      hwide (t l) hint hrest c₁ hc₁0 hc₁A hC't hres't hpole hz X (hdom ▸ hX) hout'
  have eA : X.evalAt (t l) * (X.evalAt zo) ^ (-((nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩)))
      = X.evalAt (t l) * (X.evalAt zo)⁻¹ := by rw [hord]; simp
  have eB : (infChart Γ).residue ⟨t l, hint⟩ * ((infChart Γ).residue ⟨zo, hz⟩) ^ (-((nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩)))
      = (infChart Γ).residue ⟨t l, hint⟩ * ((infChart Γ).residue ⟨zo, hz⟩)⁻¹ := by rw [hord]; simp
  have hmem' : X.evalAt (t l) * (X.evalAt zo)⁻¹ ∈ A := eA ▸ hmem
  have e3 : (⟨_, hmem'⟩ : ↥A) = ⟨_, hmem⟩ := Subtype.ext eA.symm
  refine ⟨hmem', by rw [e3]; exact hunit, ?_⟩
  rw [e3, hres, eB]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem zerosDepth_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hβle : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) ≤ 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    (∀ X ∈ (Δ.annIn ε).dom, X.ord (goodFamily Φ l) ≠ 0 →
        μ (X.evalAt (Δ.annOut ε).param) = μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l) ∧
    (∀ X ∈ (Δ.annIn ε).dom, μ (X.evalAt (goodFamily Φ l))
        ≤ max (μ (X.evalAt (Δ.annOut ε).param)) (μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  by_cases hβ0 : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0
  · obtain ⟨Q, hQ, hμQ, hzeros, -, hfac⟩ := engine_D hA Γ Δ Φ ε l hl hint hint0 hz hord hβ0 μ hμA
    refine ⟨fun X hX hXord => by rw [hzeros X hX hXord]; exact hμQ, fun X hX => ?_⟩
    obtain ⟨hu, huunit, -, hmul⟩ := hfac X hX
    rw [hmul, map_mul, abv_eq_one_of_isUnit_D μ hμA hu huunit, one_mul (μ _), ← hμQ]
    exact abv_sub_le_max_D μ hμ _ _
  ·
    have hβneg : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) < 0 :=
      lt_of_le_of_ne hβle hβ0
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
    set t := goodFamily Φ with ht
    set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc₁
    have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
    have hc₁A : c₁ ∈ A := pow_mem hpA _
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
    set zo := (Δ.annOut ε).param with hzo
    have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
      rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
    have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
    have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
      intro h0
      have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
      rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
    have hscaled : goodFamilyZero Φ.toFamData l
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
    have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
      rw [← hscaled]; exact hint0
    obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
    have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
    have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint0⟩ := Subtype.ext hscaled.symm
    have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
    have hrow : ∀ Y ∈ (Δ.annIn ε).dom, t l ∈ Y.toValuationSubring :=
      fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Y hY l hl).1
    have hpole : ∀ Y ∈ (Δ.annOut ε).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
    obtain ⟨D, hD0, hDsupp, hDord, hdeg, -⟩ :=
      AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
        (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
        (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε) hwide (t l) hint hrest c₁ hc₁0 hc₁A hC't hres't hpole
    have hordt : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [hordt, e2] at hdeg
    have hsum0 : (D.sum fun _ m => m) ≤ 0 := by rw [hdeg]; omega
    have hDzero : ∀ Y, D Y = 0 := by
      intro Y
      by_contra hne
      have hpos : 0 < D Y := lt_of_le_of_ne (hD0 Y) (Ne.symm hne)
      have hle : D Y ≤ D.sum fun _ m => m := by
        rw [Finsupp.sum]
        exact Finset.single_le_sum (fun Y' _ => hD0 Y') (Finsupp.mem_support_iff.2 hne)
      omega
    have hzf : ∀ Y ∈ (Δ.annIn ε).dom, Y.ord (t l) = 0 := fun Y hY => by rw [← hDord Y (hdom ▸ hY), hDzero]
    refine ⟨fun X hX hXord => absurd (hzf X hX) hXord, fun X hX => ?_⟩
    obtain ⟨hmem, hunit, -⟩ := outerUnit_D hA Γ Δ Φ ε l hl hint hint0 hz hord μ hμA X hX
      (fun Y hY hYord => absurd (hzf Y hY) hYord)
    obtain ⟨-, hzoX, -, hzoX0, -⟩ := (Δ.annOut ε).mem_dom X (hdom ▸ hX)
    have h1 : μ (X.evalAt (t l) * (X.evalAt zo)⁻¹) = 1 := abv_eq_one_of_isUnit_D μ hμA hmem hunit
    rw [map_mul, map_inv₀, mul_inv_eq_one₀ (μ.pos hzoX0).ne'] at h1
    rw [h1]; exact le_max_left _ _

end P2Helpers
end ModularCurve.MultCovering

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') (l₁ l₂ l₃ : Fin r) (hl₁ : 1 ≤ (l₁ : ℕ)) (hl₂ : 1 ≤ (l₂ : ℕ)) (hl₃ : 1 ≤ (l₃ : ℕ))
    (hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers)
    (hint0 : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut e).param ∈ (infChart Γ).integers) (hz' : (Δ.annOut e').param ∈ (infChart Γ).integers)

    (hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint l₁⟩) = 1)
    (hord₁' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint l₁⟩) = 1)
    (hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩) = 0)
    (hβ₁' : (nodeSrc Γ e').ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩) = 0)
    (hsep₁ : (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩)
        ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩))

    (h23 : l₂ ≠ l₃)
    (hord₂ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩) = 1)
    (hord₂' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩) = 1)
    (hord₃ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩) = 1)
    (hord₃' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩) = 1)
    (hβ₂ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint0 l₂⟩) ≤ 0)
    (hβ₃ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₃, hint0 l₃⟩) ≤ 0)
    (hn₂ : hasseExp Φ.toFamData l₁ < hasseExp Φ.toFamData l₂) (hn₃ : hasseExp Φ.toFamData l₁ < hasseExp Φ.toFamData l₃)
    (hzf₂' : ∀ R' ∈ (Δ.annIn e').dom, R'.ord (goodFamily Φ l₂) = 0)
    (hzf₃' : ∀ R' ∈ (Δ.annIn e').dom, R'.ord (goodFamily Φ l₃) = 0)
    (hdet : (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹)
        ≠ (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        ((∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R.evalAt (Δ.annOut e).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₁ * m) ∨
         (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R'.evalAt (Δ.annOut e').param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₁ * m)) →
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA R hR R' hR' hdeep hnonprop
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  set t := goodFamily Φ with ht
  set n₁ := hasseExp Φ.toFamData l₁ with hn₁
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ n₁ with hc₁
  set πr : ℝ := μ (p : AlgebraicClosure ℚ) ^ n₁ with hπr
  have hμc₁ : μ c₁ = πr := by rw [hc₁, map_pow]
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hπr0 : 0 < πr := pow_pos hμp0 _
  set zE := (Δ.annOut e).param with hzE
  set zE' := (Δ.annOut e').param with hzE'

  have hrow : ∀ (ε : Fin (mAnnuli p)), ∀ X ∈ (Δ.annIn ε).dom, ∀ i, t i ∈ X.toValuationSubring ∧ μ (X.evalAt (t i)) ≤ 1 := by
    intro ε X hX i
    by_cases hi : 1 ≤ (i : ℕ)
    · obtain ⟨hm, hlt⟩ := abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε X hX i hi
      exact ⟨hm, hlt.le⟩
    · have hi0 : (i : ℕ) = 0 := by omega
      have : t i = 1 := goodFamily_zero_eq_one p Φ i hi0
      rw [this]; exact ⟨one_mem _, by rw [Place.evalAt_one, map_one]⟩

  have hplace : ∀ (ε : Fin (mAnnuli p)), ∀ X ∈ (Δ.annIn ε).dom,
      X.IsRational ∧ (Δ.annOut ε).param ∈ X.toValuationSubring ∧ X.evalAt (Δ.annOut ε).param ≠ 0 ∧
      X.evalAt (Δ.annOut ε).param ∈ A ∧
      μ (p : AlgebraicClosure ℚ) ^ 3 < μ (X.evalAt (Δ.annOut ε).param) ∧ μ (X.evalAt (Δ.annOut ε).param) < 1 := by
    intro ε X hX
    obtain ⟨hdom, hmod, hmod0, -⟩ := Δ.twoEnded ε
    obtain ⟨hrat, hzX, ⟨hzA, hz𝔪⟩, hzX0, m, hm𝔪, hm⟩ := (Δ.annOut ε).mem_dom X (hdom ▸ hX)
    refine ⟨hrat, hzX, hzX0, hzA, ?_, abv_lt_one_of_mem_maximalIdeal_D μ hμA hz𝔪⟩
    obtain ⟨a, haA, hpa⟩ := modulus_dvd' Γ Δ ε
    have h1 : μ (p : AlgebraicClosure ℚ) ^ modulusExp ≤ μ ((Δ.annIn ε).modulus : AlgebraicClosure ℚ) := by
      have : μ (p : AlgebraicClosure ℚ) ^ modulusExp = μ ((Δ.annIn ε).modulus : AlgebraicClosure ℚ) * μ a := by
        rw [← map_pow, hpa, map_mul]
      rw [this]; exact mul_le_of_le_one_right (μ.nonneg _) ((hμA a).1 haA)
    have h2 : μ ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) < μ (X.evalAt (Δ.annOut ε).param) := by
      rw [hm, map_mul]
      have hz0 : 0 < μ (X.evalAt (Δ.annOut ε).param) := μ.pos hzX0
      have hm1 : μ (m : AlgebraicClosure ℚ) < 1 := abv_lt_one_of_mem_maximalIdeal_D μ hμA hm𝔪
      calc μ (X.evalAt (Δ.annOut ε).param) * μ (m : AlgebraicClosure ℚ) < μ (X.evalAt (Δ.annOut ε).param) * 1 :=
            mul_lt_mul_of_pos_left hm1 hz0
        _ = _ := mul_one _
    rw [show modulusExp = 3 from rfl] at h1
    rw [hmod] at h2
    exact h1.trans_lt h2
  obtain ⟨hRrat, hzER, hzER0, hzERA, hρ3, hρ1⟩ := hplace e R hR
  obtain ⟨hR'rat, hzER', hzER'0, hzER'A, hρ'3, hρ'1⟩ := hplace e' R' hR'
  set ρ : ℝ := μ (R.evalAt zE) with hρ
  set ρ' : ℝ := μ (R'.evalAt zE') with hρ'
  have hμp1 : μ (p : AlgebraicClosure ℚ) < 1 := by
    by_contra hge; push Not at hge
    have : (1 : ℝ) ≤ μ (p : AlgebraicClosure ℚ) ^ 3 := one_le_pow₀ hge
    linarith
  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) := by linarith [Real.log_nonpos hμp0.le hμp1.le]

  have close : ∀ l : Fin r, μ (p : AlgebraicClosure ℚ) ^ 3 < μ (R.evalAt (t l) - R'.evalAt (t l)) →
      |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro l hl3
    have hpos : 0 < μ (R.evalAt (t l) - R'.evalAt (t l)) := (pow_pos hμp0 3).trans hl3
    have hne : R.evalAt (t l) ≠ R'.evalAt (t l) := by
      intro h; rw [h, sub_self, map_zero] at hpos; exact lt_irrefl _ hpos
    have hbig : -Real.log (μ (R.evalAt (t l) - R'.evalAt (t l))) ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
      have h1 := Real.log_le_log (pow_pos hμp0 3) hl3.le
      rw [Real.log_pow] at h1; push_cast at h1; linarith
    exact cross_of_untied_D p A hA Γ Φ s hs μ hμ hμA R R' hRrat hR'rat (hrow e R hR) (hrow e' R' hR') l hne hbig hnonprop

  have sep_lt : ∀ l : Fin r, μ (R.evalAt (t l)) < μ (R'.evalAt (t l)) → μ (p : AlgebraicClosure ℚ) ^ 3 < μ (R'.evalAt (t l)) →
      |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro l hlt h3
    apply close l
    rw [abv_sub_eq_max_of_ne_D μ hμ hlt.ne, max_eq_right hlt.le]; exact h3
  have sep_gt : ∀ l : Fin r, μ (R'.evalAt (t l)) < μ (R.evalAt (t l)) → μ (p : AlgebraicClosure ℚ) ^ 3 < μ (R.evalAt (t l)) →
      |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro l hlt h3
    apply close l
    rw [abv_sub_eq_max_of_ne_D μ hμ hlt.ne', max_eq_left hlt.le]; exact h3

  obtain ⟨Q₁, hQ₁, hμQ₁, -, ⟨hq₁, hq₁u, hq₁res⟩, hfac₁⟩ :=
    engine_D hA Γ Δ Φ e l₁ hl₁ (hint l₁) (hint0 l₁) hz hord₁ hβ₁ μ hμA
  obtain ⟨Q₁', hQ₁', hμQ₁', -, ⟨hq₁', hq₁u', hq₁res'⟩, hfac₁'⟩ :=
    engine_D hA Γ Δ Φ e' l₁ hl₁ (hint l₁) (hint0 l₁) hz' hord₁' hβ₁' μ hμA
  obtain ⟨hu₁, hu₁unit, hu₁res, hmul₁⟩ := hfac₁ R hR
  obtain ⟨hu₁', hu₁unit', hu₁res', hmul₁'⟩ := hfac₁' R' hR'
  have hx₁ : μ (R.evalAt (t l₁)) = μ (R.evalAt zE - Q₁.evalAt zE) := by
    rw [hmul₁, map_mul, abv_eq_one_of_isUnit_D μ hμA hu₁ hu₁unit, one_mul (μ _)]
  have hy₁ : μ (R'.evalAt (t l₁)) = μ (R'.evalAt zE' - Q₁'.evalAt zE') := by
    rw [hmul₁', map_mul, abv_eq_one_of_isUnit_D μ hμA hu₁' hu₁unit', one_mul (μ _)]
  have hμa₁ : μ (Q₁.evalAt zE) = πr := hμQ₁
  have hμa₁' : μ (Q₁'.evalAt zE') = πr := hμQ₁'
  have hx₁le : μ (R.evalAt (t l₁)) ≤ max ρ πr := by rw [hx₁, ← hμa₁]; exact abv_sub_le_max_D μ hμ _ _
  have hy₁le : μ (R'.evalAt (t l₁)) ≤ max ρ' πr := by rw [hy₁, ← hμa₁']; exact abv_sub_le_max_D μ hμ _ _
  have hx₁eq : ρ ≠ πr → μ (R.evalAt (t l₁)) = max ρ πr := by
    intro hne; rw [hx₁, ← hμa₁]; exact abv_sub_eq_max_of_ne_D μ hμ (by rw [hμa₁]; exact hne)
  have hy₁eq : ρ' ≠ πr → μ (R'.evalAt (t l₁)) = max ρ' πr := by
    intro hne; rw [hy₁, ← hμa₁']; exact abv_sub_eq_max_of_ne_D μ hμ (by rw [hμa₁']; exact hne)

  obtain ⟨hzd₂, hsz₂⟩ := zerosDepth_D hA Γ Δ Φ e l₂ hl₂ (hint l₂) (hint0 l₂) hz hord₂ hβ₂ μ hμ hμA
  obtain ⟨hzd₃, hsz₃⟩ := zerosDepth_D hA Γ Δ Φ e l₃ hl₃ (hint l₃) (hint0 l₃) hz hord₃ hβ₃ μ hμ hμA
  obtain ⟨hm₂', hun₂', hres₂'⟩ := outerUnit_D hA Γ Δ Φ e' l₂ hl₂ (hint l₂) (hint0 l₂) hz' hord₂' μ hμA R' hR'
    (fun Y hY hYo => absurd (hzf₂' Y hY) hYo)
  obtain ⟨hm₃', hun₃', hres₃'⟩ := outerUnit_D hA Γ Δ Φ e' l₃ hl₃ (hint l₃) (hint0 l₃) hz' hord₃' μ hμA R' hR'
    (fun Y hY hYo => absurd (hzf₃' Y hY) hYo)
  have hunit_size : ∀ {u v : AlgebraicClosure ℚ} (hm : u * v⁻¹ ∈ A), IsUnit (⟨_, hm⟩ : ↥A) → v ≠ 0 → μ u = μ v := by
    intro u v hm hun hv0
    have h1 : μ (u * v⁻¹) = 1 := abv_eq_one_of_isUnit_D μ hμA hm hun
    rwa [map_mul, map_inv₀, mul_inv_eq_one₀ (μ.pos hv0).ne'] at h1
  have hy₂ : μ (R'.evalAt (t l₂)) = ρ' := hunit_size hm₂' hun₂' hzER'0
  have hy₃ : μ (R'.evalAt (t l₃)) = ρ' := hunit_size hm₃' hun₃' hzER'0
  have hpow₂ : μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₂ < πr := pow_lt_pow_right_of_lt_one₀ hμp0 hμp1 hn₂
  have hpow₃ : μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₃ < πr := pow_lt_pow_right_of_lt_one₀ hμp0 hμp1 hn₃

  have hdeepR : ρ ≤ πr ∨ ρ' ≤ πr := by
    rcases hdeep with ⟨m, hmA, hm⟩ | ⟨m, hmA, hm⟩
    · left
      rw [hρ, show R.evalAt zE = R.evalAt (Δ.annOut e).param from rfl, hm, map_mul, map_pow]
      exact mul_le_of_le_one_right (pow_nonneg (μ.nonneg _) _) ((hμA m).1 hmA)
    · right
      rw [hρ', show R'.evalAt zE' = R'.evalAt (Δ.annOut e').param from rfl, hm, map_mul, map_pow]
      exact mul_le_of_le_one_right (pow_nonneg (μ.nonneg _) _) ((hμA m).1 hmA)

  rcases lt_trichotomy ρ πr with hρlt | hρeq | hρgt
  · rcases lt_trichotomy ρ' πr with hρ'lt | hρ'eq | hρ'gt
    ·
      apply close l₁

      have hzc : R.evalAt zE * c₁⁻¹ ∈ A := (hμA _).2 (by
        rw [map_mul, map_inv₀, hμc₁]; exact (mul_inv_le_iff₀ hπr0).2 (by rw [one_mul πr]; exact hρlt.le))
      have hzc' : R'.evalAt zE' * c₁⁻¹ ∈ A := (hμA _).2 (by
        rw [map_mul, map_inv₀, hμc₁]; exact (mul_inv_le_iff₀ hπr0).2 (by rw [one_mul πr]; exact hρ'lt.le))
      have hzcres : IsLocalRing.residue ↥A ⟨_, hzc⟩ = 0 := by
        apply (IsLocalRing.residue_eq_zero_iff _).2
        apply mem_maximalIdeal_of_abv_lt_one_D μ hμA hzc
        rw [map_mul, map_inv₀, hμc₁]; exact (mul_inv_lt_iff₀ hπr0).2 (by rw [one_mul πr]; exact hρlt)
      have hzcres' : IsLocalRing.residue ↥A ⟨_, hzc'⟩ = 0 := by
        apply (IsLocalRing.residue_eq_zero_iff _).2
        apply mem_maximalIdeal_of_abv_lt_one_D μ hμA hzc'
        rw [map_mul, map_inv₀, hμc₁]; exact (mul_inv_lt_iff₀ hπr0).2 (by rw [one_mul πr]; exact hρ'lt)

      set X₁A : ↥A := ⟨_, hu₁⟩ * (⟨_, hzc⟩ - ⟨_, hq₁⟩) with hX₁A
      set Y₁A : ↥A := ⟨_, hu₁'⟩ * (⟨_, hzc'⟩ - ⟨_, hq₁'⟩) with hY₁A
      have hX₁val : (X₁A : AlgebraicClosure ℚ) = R.evalAt (t l₁) * c₁⁻¹ := by
        rw [hX₁A]; push_cast; rw [hmul₁]; ring
      have hY₁val : (Y₁A : AlgebraicClosure ℚ) = R'.evalAt (t l₁) * c₁⁻¹ := by
        rw [hY₁A]; push_cast; rw [hmul₁']; ring

      set w₁ := (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨t l₁, hint l₁⟩ * ((infChart Γ).residue ⟨zE, hz⟩)⁻¹) with hw₁
      set w₁' := (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨t l₁, hint l₁⟩ * ((infChart Γ).residue ⟨zE', hz'⟩)⁻¹) with hw₁'
      set v₁ := (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩) with hv₁
      set v₁' := (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩) with hv₁'
      have hw₁0 : w₁ ≠ 0 := by
        rw [← hu₁res]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu₁unit
      have hw₁'0 : w₁' ≠ 0 := by
        rw [← hu₁res']; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu₁unit'
      have hX₁res : IsLocalRing.residue ↥A X₁A = v₁ := by
        rw [hX₁A, map_mul, map_sub, hu₁res, hzcres, hq₁res, zero_sub]
        field_simp
      have hY₁res : IsLocalRing.residue ↥A Y₁A = v₁' := by
        rw [hY₁A, map_mul, map_sub, hu₁res', hzcres', hq₁res', zero_sub]
        field_simp
      have hDres : IsLocalRing.residue ↥A (X₁A - Y₁A) ≠ 0 := by
        rw [map_sub, hX₁res, hY₁res, sub_ne_zero]; exact hsep₁
      have hDunit : IsUnit (X₁A - Y₁A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hDres
      have hDval : ((X₁A - Y₁A : ↥A) : AlgebraicClosure ℚ) = (R.evalAt (t l₁) - R'.evalAt (t l₁)) * c₁⁻¹ := by
        push_cast; rw [hX₁val, hY₁val]; ring
      have hμD : μ ((R.evalAt (t l₁) - R'.evalAt (t l₁)) * c₁⁻¹) = 1 := by
        rw [← hDval]; exact abv_eq_one_of_isUnit_D μ hμA (X₁A - Y₁A).2 (by first | exact hDunit | simpa using hDunit | simpa +zetaDelta using hDunit)
      rw [map_mul, map_inv₀, mul_inv_eq_one₀ (μ.pos hc₁0).ne', hμc₁] at hμD
      rw [hμD]; exact hρ3.trans hρlt
    ·
      apply sep_lt l₂
      · calc μ (R.evalAt (t l₂)) ≤ max ρ (μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₂) := hsz₂ R hR
          _ < πr := max_lt hρlt hpow₂
          _ = μ (R'.evalAt (t l₂)) := by rw [hy₂, hρ'eq]
      · rw [hy₂]; exact hρ'3
    ·
      apply sep_lt l₁
      · calc μ (R.evalAt (t l₁)) ≤ max ρ πr := hx₁le
          _ = πr := max_eq_right hρlt.le
          _ < ρ' := hρ'gt
          _ = μ (R'.evalAt (t l₁)) := by rw [hy₁eq hρ'gt.ne', max_eq_left hρ'gt.le]
      · rw [hy₁eq hρ'gt.ne', max_eq_left hρ'gt.le]; exact hρ'3
  · rcases lt_trichotomy ρ' πr with hρ'lt | hρ'eq | hρ'gt
    ·
      obtain ⟨hm₂, hun₂, -⟩ := outerUnit_D hA Γ Δ Φ e l₂ hl₂ (hint l₂) (hint0 l₂) hz hord₂ μ hμA R hR
        (fun Y hY hYo => by rw [hzd₂ Y hY hYo]; exact hpow₂.trans_eq hρeq.symm)
      have hx₂ : μ (R.evalAt (t l₂)) = ρ := hunit_size hm₂ hun₂ hzER0
      apply sep_gt l₂
      · rw [hx₂, hy₂, hρeq]; exact hρ'lt
      · rw [hx₂]; exact hρ3
    ·
      obtain ⟨hm₂, hun₂, hres₂⟩ := outerUnit_D hA Γ Δ Φ e l₂ hl₂ (hint l₂) (hint0 l₂) hz hord₂ μ hμA R hR
        (fun Y hY hYo => by rw [hzd₂ Y hY hYo]; exact hpow₂.trans_eq hρeq.symm)
      obtain ⟨hm₃, hun₃, hres₃⟩ := outerUnit_D hA Γ Δ Φ e l₃ hl₃ (hint l₃) (hint0 l₃) hz hord₃ μ hμA R hR
        (fun Y hY hYo => by rw [hzd₃ Y hY hYo]; exact hpow₃.trans_eq hρeq.symm)
      by_cases h2 : μ (p : AlgebraicClosure ℚ) ^ 3 < μ (R.evalAt (t l₂) - R'.evalAt (t l₂))
      · exact close l₂ h2
      by_cases h3 : μ (p : AlgebraicClosure ℚ) ^ 3 < μ (R.evalAt (t l₃) - R'.evalAt (t l₃))
      · exact close l₃ h3
      exfalso
      push Not at h2 h3

      have hρρ' : μ (R'.evalAt zE') = μ (R.evalAt zE) := by
        show ρ' = ρ; rw [hρeq, hρ'eq]
      have hlamA : R'.evalAt zE' * (R.evalAt zE)⁻¹ ∈ A := (hμA _).2 (by
        rw [map_mul, map_inv₀, hρρ', mul_inv_cancel₀ (μ.pos hzER0).ne'])

      have hsmall : ∀ (l : Fin r) (hm : R.evalAt (t l) * (R.evalAt zE)⁻¹ ∈ A)
          (hm' : R'.evalAt (t l) * (R'.evalAt zE')⁻¹ ∈ A),
          μ (R.evalAt (t l) - R'.evalAt (t l)) ≤ μ (p : AlgebraicClosure ℚ) ^ 3 →
          IsLocalRing.residue ↥A ⟨_, hm⟩ = IsLocalRing.residue ↥A ⟨_, hlamA⟩ * IsLocalRing.residue ↥A ⟨_, hm'⟩ := by
        intro l hm hm' hle
        have hval : ((⟨_, hm⟩ - ⟨_, hlamA⟩ * ⟨_, hm'⟩ : ↥A) : AlgebraicClosure ℚ)
            = (R.evalAt (t l) - R'.evalAt (t l)) * (R.evalAt zE)⁻¹ := by
          have hz1 : R'.evalAt zE' ≠ 0 := hzER'0
          have hz2 : R.evalAt zE ≠ 0 := hzER0
          push_cast
          field_simp
        have hlt1 : μ ((R.evalAt (t l) - R'.evalAt (t l)) * (R.evalAt zE)⁻¹) < 1 := by
          rw [map_mul, map_inv₀]
          refine (mul_inv_lt_iff₀ (μ.pos hzER0)).2 ?_
          rw [one_mul (μ _)]; exact hle.trans_lt hρ3
        have hres0 : IsLocalRing.residue ↥A (⟨_, hm⟩ - ⟨_, hlamA⟩ * ⟨_, hm'⟩) = 0 := by
          apply (IsLocalRing.residue_eq_zero_iff _).2
          have hmem : ((⟨_, hm⟩ - ⟨_, hlamA⟩ * ⟨_, hm'⟩ : ↥A) : AlgebraicClosure ℚ) ∈ A := SetLike.coe_mem _
          have := mem_maximalIdeal_of_abv_lt_one_D μ hμA hmem (by rw [hval]; exact hlt1)
          first | exact this | simpa using this | simpa +zetaDelta using this
        rw [map_sub, map_mul, sub_eq_zero] at hres0
        exact hres0
      have e₂ := hsmall l₂ hm₂ hm₂' h2
      have e₃ := hsmall l₃ hm₃ hm₃' h3
      rw [hres₂, hres₂'] at e₂
      rw [hres₃, hres₃'] at e₃
      apply hdet
      rw [e₂, e₃]; ring
    ·
      apply sep_lt l₁
      · calc μ (R.evalAt (t l₁)) ≤ max ρ πr := hx₁le
          _ = πr := by rw [hρeq, max_self]
          _ < ρ' := hρ'gt
          _ = μ (R'.evalAt (t l₁)) := by rw [hy₁eq hρ'gt.ne', max_eq_left hρ'gt.le]
      · rw [hy₁eq hρ'gt.ne', max_eq_left hρ'gt.le]; exact hρ'3
  · rcases lt_trichotomy ρ' πr with hρ'lt | hρ'eq | hρ'gt
    ·
      apply sep_gt l₁
      · calc μ (R'.evalAt (t l₁)) ≤ max ρ' πr := hy₁le
          _ = πr := max_eq_right hρ'lt.le
          _ < ρ := hρgt
          _ = μ (R.evalAt (t l₁)) := by rw [hx₁eq hρgt.ne', max_eq_left hρgt.le]
      · rw [hx₁eq hρgt.ne', max_eq_left hρgt.le]; exact hρ3
    ·
      apply sep_gt l₁
      · calc μ (R'.evalAt (t l₁)) ≤ max ρ' πr := hy₁le
          _ = πr := by rw [hρ'eq, max_self]
          _ < ρ := hρgt
          _ = μ (R.evalAt (t l₁)) := by rw [hx₁eq hρgt.ne', max_eq_left hρgt.le]
      · rw [hx₁eq hρgt.ne', max_eq_left hρgt.le]; exact hρ3
    ·
      exfalso
      rcases hdeepR with h | h
      · exact (not_le.2 hρgt) h
      · exact (not_le.2 hρ'gt) h

end S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms (solution)
