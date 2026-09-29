-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b6afbdb8-a845-5f10-a1aa-c49979a65784

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
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
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
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
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
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve"

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem cross_of_big_coordinate_D (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (R Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hRrat : R.IsRational) (hQrat : Q.IsRational)
    (hR : ∀ i, goodFamily Φ i ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ i)) ≤ 1)
    (hQ : ∀ i, goodFamily Φ i ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ i)) ≤ 1)
    (l : Fin r) (hl : 1 ≤ (l : ℕ)) (hlt : μ (Q.evalAt (goodFamily Φ l)) < μ (R.evalAt (goodFamily Φ l)))
    (hbig : -Real.log (μ (R.evalAt (goodFamily Φ l))) ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))))
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
  have hlt' : μ (y l) < μ (x l) := by rw [hxeval, hyeval]; exact hlt
  have hxl0 : 0 < μ (x l) := lt_of_le_of_lt (μ.nonneg _) hlt'

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
  have hdiff : μ (x l - y l) = μ (x l) := by
    apply le_antisymm
    · exact (hsub _ _).trans (max_le le_rfl hlt'.le)
    · have h := hμ (x l - y l) (y l)
      rw [sub_add_cancel] at h
      rcases le_max_iff.mp h with h' | h'
      · exact h'
      · exact absurd h' (not_le.mpr hlt')
  have hm1 : x o * y l - x l * y o ≠ 0 := by
    rw [hxo, hyo, one_mul, mul_one]
    intro h0
    have : μ (x l - y l) = 0 := by rw [← neg_sub, AbsoluteValue.map_neg, h0, map_zero]
    rw [hdiff] at this
    exact hxl0.ne' this
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
  have hS_ge : μ (x l) ≤ ⨆ i, μ (x i - y i) := by
    rw [← hdiff]; exact le_ciSup (Finite.bddAbove_range fun i => μ (x i - y i)) l
  have hS0 : 0 < ⨆ i, μ (x i - y i) := lt_of_lt_of_le hxl0 hS_ge
  have hprox_nonneg : 0 ≤ prox μ x y := by
    rw [hS]; exact neg_nonneg.mpr (Real.log_nonpos hS0.le hS_le)
  have hprox_le : prox μ x y ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    rw [hS]
    refine (neg_le_neg (Real.log_le_log hxl0 hS_ge)).trans ?_
    rw [hxeval]; exact hbig

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
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero goodFamily_zero_eq_one abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

theorem prox_symm_D {K : Type*} [Field K] {r : ℕ} (μ : AbsoluteValue K ℝ) (x y : Fin r → K) :
    prox μ x y = prox μ y x := by
  unfold prox
  have h : (fun q : Fin r × Fin r => μ (y q.1 * x q.2 - y q.2 * x q.1))
      = fun q : Fin r × Fin r => μ (x q.1 * y q.2 - x q.2 * y q.1) := by
    funext q
    rw [show y q.1 * x q.2 - y q.2 * x q.1 = -(x q.1 * y q.2 - x q.2 * y q.1) by ring, AbsoluteValue.map_neg]
  simp only [h]
  ring

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

end ModularCurve.MultCovering

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') (l₁ : Fin r) (hl₁ : 1 ≤ (l₁ : ℕ))
    (hint₁ : goodFamily Φ l₁ ∈ (infChart Γ).integers)
    (hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint₁⟩) = 1)
    (hord₁' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint₁⟩) = 1)
    (hint0₁ : goodFamilyZero Φ.toFamData l₁ ∈ (zeroChart Γ).integers)
    (hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩) = 0)
    (hzf₁' : ∀ R' ∈ (Δ.annIn e').dom, R'.ord (goodFamily Φ l₁) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
          R.evalAt (Δ.annOut e).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₁ * m) →
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA R hR R' hR' hdeep hnonprop
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set n₁ := hasseExp Φ.toFamData l₁ with hn₁
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ n₁ with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 hpA

  have hrow : ∀ (e₀ : Fin (mAnnuli p)), ∀ X ∈ (Δ.annIn e₀).dom, ∀ i, t i ∈ X.toValuationSubring ∧ μ (X.evalAt (t i)) ≤ 1 := by
    intro e₀ X hX i
    by_cases hi : 1 ≤ (i : ℕ)
    · obtain ⟨hm, hlt⟩ := abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e₀ X hX i hi
      exact ⟨hm, hlt.le⟩
    · have hi0 : (i : ℕ) = 0 := by omega
      have : t i = 1 := goodFamily_zero_eq_one p Φ i hi0
      rw [this]; exact ⟨one_mem _, by rw [Place.evalAt_one, map_one]⟩

  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨-, hzoC, hzoord, -⟩ := Δ.attached_tgt e
  set C := chart Γ (tgt p e) with hC_def
  set C' := chart Γ (src p e) with hC'_def
  set zo := (Δ.annOut e).param with hzo
  have hmod0' : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn e).param * zo = zo * (Δ.annIn e).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hx : (nodeTgt Γ e).IsRational := by
    apply isRational_of_deg_eq_one
    exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)
  have hx' : (nodeSrc Γ e).IsRational := by
    apply isRational_of_deg_eq_one
    exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p)
  have hCt : t l₁ ∈ C.integers := hint₁
  have hordt : (nodeTgt Γ e).ord (C.residue ⟨t l₁, hCt⟩) = 1 := hord₁
  have hrest : C.residue ⟨t l₁, hCt⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordt; exact zero_ne_one hordt
  have hscaled : goodFamilyZero Φ.toFamData l₁
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l₁ := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l₁ ∈ C'.integers := by
    rw [← hscaled]; exact hint0₁
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : C'.integers) = ⟨_, hintZ l₁⟩ := Subtype.ext hscaled.symm
  have hres't : C'.residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l₁
  have hord't : (nodeSrc Γ e).ord (C'.residue ⟨_, hC't⟩) = 0 := by
    have e2 : (⟨_, hC't⟩ : C'.integers) = ⟨_, hint0₁⟩ := Subtype.ext hscaled.symm
    rw [e2]; exact hβ₁
  have hpole : ∀ X ∈ (Δ.annOut e).dom, 0 ≤ X.ord (t l₁) := fun X hX =>
    X.ord_nonneg_of_mem (hrow e X (hdom ▸ hX) l₁).1
  obtain ⟨Q₁, hQ₁dom, hordQ₁, hordP, hμQ₁, -, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' C (nodeTgt Γ e) (Δ.attached_tgt e) hx
      C' (nodeSrc Γ e) (Δ.attached_src e) hx' hwide (t l₁) hCt hrest hordt c₁ hc₁0 hc₁A hC't hres't hord't hpole hzoC
  have hRout : R ∈ (Δ.annOut e).dom := hdom ▸ hR
  obtain ⟨hRrat, hzoR, -, hzoR0, -⟩ := (Δ.annOut e).mem_dom R hRout
  have htR : t l₁ ∈ R.toValuationSubring := (hrow e R hR l₁).1
  have hsmall : μ (R.evalAt (t l₁)) ≤ μ c₁ := by
    by_cases hRQ : R = Q₁
    ·
      have hev : R.evalAt (t l₁) = 0 := by
        by_contra hne
        have := ord_eq_zero_of_evalAt_ne_zero_D R htR hne
        rw [hRQ, hordQ₁] at this; exact one_ne_zero this
      rw [hev, map_zero]; exact μ.nonneg _
    · obtain ⟨hu, huunit, -⟩ := hfac R hRout
      set a₁ := Q₁.evalAt (Δ.annOut e).param with ha₁
      have hwR : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁ ∈ R.toValuationSubring :=
        sub_mem hzoR (R.algebraMap_mem' a₁)
      have hwev : R.evalAt (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁) = R.evalAt zo - a₁ := by
        rw [evalAt_sub_D R hRrat hzoR (R.algebraMap_mem' a₁), evalAt_algebraMap_D]
      have hwne : R.evalAt zo - a₁ ≠ 0 := by
        rw [sub_ne_zero]
        intro h1; apply hRQ
        obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := (Δ.annOut e).mem_dom Q₁ hQ₁dom
        obtain ⟨P₀, -, huniq⟩ := (Δ.annOut e).existsUnique_evalAt_eq ⟨a₁, haA⟩ ha𝔪 ha0 hm
        exact (huniq R ⟨hRout, h1⟩).trans (huniq Q₁ ⟨hQ₁dom, rfl⟩).symm
      have hev0 : R.evalAt (0 : modularFunctionFieldBar (1 * p)) = 0 := by
        rw [R.evalAt_of_mem (zero_mem _)]
        have : (⟨(0 : modularFunctionFieldBar (1 * p)), zero_mem _⟩ : R.toValuationSubring) = 0 := rfl
        rw [this, map_zero, ← map_zero (algebraMap (AlgebraicClosure ℚ) R.ResidueField), R.residueInv_algebraMap]
      have hw0 : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁ ≠ 0 := by
        intro h0; apply hwne; rw [← hwev, h0, hev0]
      have hwinvR : (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁)⁻¹ ∈ R.toValuationSubring := by
        have hordw : R.ord (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁) = 0 :=
          ord_eq_zero_of_evalAt_ne_zero_D R hwR (by rw [hwev]; exact hwne)
        exact R.mem_of_ord_nonneg (inv_ne_zero hw0) (by rw [Place.ord_inv, hordw]; norm_num)
      have hprod : R.evalAt (t l₁) = R.evalAt (t l₁ * (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁)⁻¹)
          * R.evalAt (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁) := by
        rw [← evalAt_mul_D R hRrat (mul_mem htR hwinvR) hwR, inv_mul_cancel_right₀ hw0]
      have hμu : μ (R.evalAt (t l₁ * (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) a₁)⁻¹)) = 1 :=
        abv_eq_one_of_isUnit_D μ hμA hu huunit
      rw [hprod, map_mul, hμu, one_mul (μ _), hwev]
      obtain ⟨m, hmA, hm⟩ := hdeep
      have hsub : μ (R.evalAt zo - a₁) ≤ max (μ (R.evalAt zo)) (μ a₁) := by
        rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ a₁]; exact hμ _ _
      refine hsub.trans (max_le ?_ (le_of_eq hμQ₁))
      rw [show R.evalAt zo = R.evalAt (Δ.annOut e).param from rfl, hm, map_mul, hc₁]
      exact mul_le_of_le_one_right (μ.nonneg _) ((hμA m).1 hmA)

  obtain ⟨hpow', -, htube'⟩ := abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
    p A hA Γ Δ Φ e' l₁ hint₁ hord₁' hzf₁' μ hμA
  obtain ⟨hR'rat, htR', hμtR', hbigger⟩ := htube' R' hR'
  have hlt : μ (R.evalAt (t l₁)) < μ (R'.evalAt (t l₁)) := by
    rw [hμtR']
    refine hsmall.trans_lt ?_
    rw [hc₁, map_pow, hn₁, hpow']; exact hbigger
  obtain ⟨a, haA, hpa⟩ := modulus_dvd' Γ Δ e'
  have hmodge : μ (p : AlgebraicClosure ℚ) ^ modulusExp ≤ μ ((Δ.annIn e').modulus : AlgebraicClosure ℚ) := by
    have h1 : μ (p : AlgebraicClosure ℚ) ^ modulusExp = μ ((Δ.annIn e').modulus : AlgebraicClosure ℚ) * μ a := by
      rw [← map_pow, hpa, map_mul]
    rw [h1]; exact mul_le_of_le_one_right (μ.nonneg _) ((hμA a).1 haA)
  have hbig : -Real.log (μ (R'.evalAt (t l₁))) ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    have hgt : μ (p : AlgebraicClosure ℚ) ^ modulusExp < μ (R'.evalAt (t l₁)) := by
      rw [hμtR']; exact hmodge.trans_lt hbigger
    have h1 := Real.log_le_log (pow_pos hμp0 _) hgt.le
    rw [Real.log_pow, show (modulusExp : ℝ) = 3 by norm_num [modulusExp]] at h1
    linarith

  have hnonprop' : ∃ i' j', evalVec s R' i' * evalVec s R j' ≠ evalVec s R' j' * evalVec s R i' := by
    obtain ⟨i', j', hij⟩ := hnonprop
    exact ⟨j', i', fun h => hij (by rw [mul_comm (evalVec s R i'), mul_comm (evalVec s R j')]; exact h)⟩
  have key := cross_of_big_coordinate_D p A hA Γ Φ s hs μ hμ hμA R' R hR'rat hRrat
    (fun i => hrow e' R' hR' i) (fun i => hrow e R hR i) l₁ hl₁ hlt hbig hnonprop'
  rw [prox_symm_D] at key
  exact key

end S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree (solution)
