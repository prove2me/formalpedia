-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_ord_one_of_zeroFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1b0e9a68-b626-5604-bb9c-c808f0bd489e

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_ord_one_of_zeroFree
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_ord_one_of_zeroFree.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_ord_one_of_zeroFree.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar PlaceSpecialization.jFun PlaceSpecialization jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue nodeTgt linkMatrix linkMatrixInv linkBudget compConst compConst_eq hasseExp goodFamilyZero FamCtx goodFamily linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec goodFamily_zero_eq_one abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero"
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

theorem not_isSSCentred_cuspInftyBar (a : IsLocalRing.ResidueField ↥A) : ¬ IsSSCentred p A (cuspInftyBar (1 * p)) a := by
  rintro ⟨⟨x, -, hx⟩, -⟩

  have hj : (cuspInftyBar (1 * p)).ord (PlaceSpecialization.jFun (q := p)) = -1 :=
    ModularCurve.ord_cuspInftyBar_coeffEmb_jq (1 * p)
  have hj0 : (PlaceSpecialization.jFun (q := p) : ↥(modularFunctionFieldBar (1 * p))) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hj; norm_num at hj
  by_cases hx0 : (x : AlgebraicClosure ℚ) = 0
  · rw [hx0, map_zero, sub_zero, hj] at hx; norm_num at hx
  · have hc0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (-(x : AlgebraicClosure ℚ)) ≠ 0 :=
      (map_ne_zero _).2 (neg_ne_zero.2 hx0)
    have hlt : (cuspInftyBar (1 * p)).ord (PlaceSpecialization.jFun (q := p))
        < (cuspInftyBar (1 * p)).ord (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (-(x : AlgebraicClosure ℚ))) := by
      rw [Place.ord_algebraMap, hj]; norm_num
    have := Place.ord_add_eq_of_lt (cuspInftyBar (1 * p)) hj0 hc0 hlt
    rw [map_neg, ← sub_eq_add_neg, hj] at this
    rw [this] at hx; norm_num at hx

theorem ne_cuspInftyBar_of_mem_annIn_dom (e : Fin (mAnnuli p))
    (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hP : P ∈ (Δ.annIn e).dom) : P ≠ cuspInftyBar (1 * p) := by
  intro h
  have := (Δ.mem_dom_iff e P).mp hP
  rw [h] at this
  exact not_isSSCentred_cuspInftyBar _ this

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
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar PlaceSpecialization.jFun PlaceSpecialization jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue nodeTgt linkMatrix linkMatrixInv linkBudget compConst compConst_eq hasseExp goodFamilyZero FamCtx goodFamily linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec goodFamily_zero_eq_one abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero"
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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (e : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hzf : ∀ R ∈ (Δ.annIn e).dom, R.ord (goodFamily Φ l) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (∃ i' j', evalVec s R i' * evalVec s Q j' ≠ evalVec s R j' * evalVec s Q i') →
        |prox μ (evalVec s R) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA R hR Q hQ hnonprop
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 hpA
  obtain ⟨hpow, -, htube⟩ := abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero p A hA Γ Δ Φ e l hint hord hzf μ hμA
  obtain ⟨hRrat, htlR, hμtl, hbigger⟩ := htube R hR
  obtain ⟨hQrat, hQall⟩ := abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom p A hA Γ Φ μ hμA Q hQ
  have hRall : ∀ i, goodFamily Φ i ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ i)) ≤ 1 := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · obtain ⟨hm, hlt⟩ := abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e R hR i hi
      exact ⟨hm, hlt.le⟩
    · have hi0 : (i : ℕ) = 0 := by omega
      rw [goodFamily_zero_eq_one p Φ i hi0]
      exact ⟨one_mem _, by rw [Place.evalAt_one, map_one]⟩
  have hQall' : ∀ i, goodFamily Φ i ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ i)) ≤ 1 := fun i =>
    ⟨(hQall i).1, (hQall i).2.trans (pow_le_one₀ (μ.nonneg _) hμp1)⟩
  have hlt : μ (Q.evalAt (goodFamily Φ l)) < μ (R.evalAt (goodFamily Φ l)) := by
    rw [hμtl]; exact (((hQall l).2.trans_eq hpow)).trans_lt hbigger

  obtain ⟨a, haA, hpa⟩ := modulus_dvd' Γ Δ e
  have hmodge : μ (p : AlgebraicClosure ℚ) ^ modulusExp ≤ μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) := by
    have h1 : μ (p : AlgebraicClosure ℚ) ^ modulusExp = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * μ a := by
      rw [← map_pow, hpa, map_mul]
    rw [h1]
    exact mul_le_of_le_one_right (μ.nonneg _) ((hμA a).1 haA)
  have htlR_gt : μ (p : AlgebraicClosure ℚ) ^ modulusExp < μ (R.evalAt (goodFamily Φ l)) := by
    rw [hμtl]; exact hmodge.trans_lt hbigger
  have hbig : -Real.log (μ (R.evalAt (goodFamily Φ l))) ≤ 3 * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    have h1 := Real.log_le_log (pow_pos hμp0 _) htlR_gt.le
    rw [Real.log_pow] at h1
    have h3 : (modulusExp : ℝ) = 3 := by norm_num [modulusExp]
    rw [h3] at h1
    linarith
  exact cross_of_big_coordinate_D p A hA Γ Φ s hs μ hμ hμA R Q hRrat hQrat hRall hQall' l hl hlt hbig hnonprop

end S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_ord_one_of_zeroFree
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_ord_one_of_zeroFree (solution)
