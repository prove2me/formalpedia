-- Prove2me | solution 1 for ModularCurve.MultCovering.residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6463c5c1-330b-5030-8dda-776afd7372bc

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_one_of_forall_widthOne
import Theorems.Thm_ModularCurve_MultCovering_neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar PlaceSpecialization.jFun PlaceSpecialization deg_charLGeomPlaceOfPoint jWidth jWidth_of_ne deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt hasseExp goodFamilyZero FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero one_le_hasseExp goodFamily_zero_eq_one infChart_goodFamily_residue_ne_zero abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero hasseExp_zero hasseExp_le_one_of_forall_widthOne neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one"
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

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728)
    (e : Fin (mAnnuli p)) (le : Fin r) (hle : 1 ≤ (le : ℕ))
    (hint : goodFamily Φ le ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ le, hint⟩) = 1)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∀ i : Fin r, ∃ h0 : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨_, h0⟩ ∈ (nodeSrc Γ e).toValuationSubring ∧
      ∀ R ∈ (Δ.annIn e).dom, ∃ hmem : R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) ∈ A,
        IsLocalRing.residue ↥A ⟨_, hmem⟩ = (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨_, h0⟩) := by
  intro i
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hwidth : jWidth (ssValue Γ e) = 1 := jWidth_of_ne (hw e).1 (hw e).2
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hintI, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZ2, hZ2⟩ := neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero p A hA Γ Δ Φ hw
  have hzf := ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one p A hA Γ Δ Φ e hwidth le hle hint hord
  obtain ⟨hpow, ⟨h0le, hordle⟩, htube⟩ :=
    abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero p A hA Γ Δ Φ e le hint hord hzf μ hμA

  have huC : goodFamilyZero Φ.toFamData le ∈ (zeroChart Γ).integers := hintZ le
  have hures : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData le, huC⟩ ≠ 0 := hresZ le
  have huinv : (goodFamilyZero Φ.toFamData le)⁻¹ ∈ (zeroChart Γ).integers := vs_inv_mem_of_isUnit_D huC (chart_isUnit_of_residue_ne_zero_D (zeroChart Γ) huC hures)
  have hg : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ ∈ (zeroChart Γ).integers := mul_mem (hintZ i) huinv
  have hgres : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹, hg⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hintZ i⟩ * ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData le, huC⟩)⁻¹ := by
    have e1 : (⟨goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹, hg⟩ : (zeroChart Γ).integers) = ⟨goodFamilyZero Φ.toFamData i, hintZ i⟩ * ⟨(goodFamilyZero Φ.toFamData le)⁻¹, huinv⟩ := Subtype.ext rfl
    rw [e1, map_mul, chart_residue_inv_D (zeroChart Γ) huC hures huinv]
  have hgres0 : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹, hg⟩ ≠ 0 := by rw [hgres]; exact mul_ne_zero (hresZ i) (inv_ne_zero hures)

  have hordu : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData le, huC⟩) = -1 := by
    have e1 : (⟨goodFamilyZero Φ.toFamData le, huC⟩ : (zeroChart Γ).integers) = ⟨goodFamilyZero Φ.toFamData le, h0le⟩ := Subtype.ext rfl
    rw [e1]; exact hordle
  have hordv : -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hintZ i⟩) := by
    have e1 : (⟨goodFamilyZero Φ.toFamData i, hintZ i⟩ : (zeroChart Γ).integers) = ⟨goodFamilyZero Φ.toFamData i, hintZ2 i⟩ := Subtype.ext rfl
    rw [e1]; exact hZ2 e i
  have hordg : 0 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹, hg⟩) := by
    rw [hgres, (nodeSrc Γ e).ord_mul (hresZ i) (inv_ne_zero hures), Place.ord_inv, hordu]; linarith [hordv]
  refine ⟨hg, (nodeSrc Γ e).mem_of_ord_nonneg hgres0 hordg, fun R hR => ?_⟩
  obtain ⟨hRrat, htleR, hμtle, hbig⟩ := htube R hR

  have hnle : hasseExp Φ.toFamData le = 1 :=
    le_antisymm (hasseExp_le_one_of_forall_widthOne p A hA Γ Δ Φ hw le) (one_le_hasseExp p A hA Γ Φ le hle)
  have hu_eq : goodFamilyZero Φ.toFamData le = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ))⁻¹
      * goodFamily Φ le := by
    rw [goodFamilyZero_eq_inv_mul', hnle, pow_one]
  have htle0 : goodFamily Φ le ≠ 0 := goodFamily_ne_zero' Φ le
  have hP : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ) ≠ 0 :=
    (map_ne_zero _).2 hp0

  have hmodp : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = p := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e, hwidth, pow_one]; rfl
  have hdeg : (nodeSrc Γ e).IsRational :=
    isRational_of_deg_eq_one _ (by unfold nodeSrc; exact deg_charLGeomPlaceOfPoint _ _)

  have hpos : 0 < μ (R.evalAt (goodFamily Φ le)) := by rw [hμtle]; exact lt_of_le_of_lt (μ.nonneg _) hbig
  have htleR0 : R.evalAt (goodFamily Φ le) ≠ 0 := fun h0 => by rw [h0, map_zero] at hpos; exact lt_irrefl _ hpos
  have hinvR : (goodFamily Φ le)⁻¹ ∈ R.toValuationSubring :=
    R.mem_of_ord_nonneg (inv_ne_zero htle0) (by rw [Place.ord_inv, hzf R hR]; simp)
  have hevinv : R.evalAt (goodFamily Φ le)⁻¹ = (R.evalAt (goodFamily Φ le))⁻¹ := by
    have h1 := evalAt_mul_D R hRrat htleR hinvR
    rw [mul_inv_cancel₀ htle0, Place.evalAt_one] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  by_cases hi : (i : ℕ) = 0
  ·
    have hti : goodFamily Φ i = 1 := goodFamily_zero_eq_one p Φ i hi
    have hv1 : goodFamilyZero Φ.toFamData i = 1 := by
      rw [goodFamilyZero_eq_inv_mul', hasseExp_zero Φ i hi, pow_zero, map_one, inv_one, hti, mul_one]
    have hg_eq : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : AlgebraicClosure ℚ)
        * (goodFamily Φ le)⁻¹ := by
      rw [hv1, hu_eq, mul_inv, inv_inv]; exact one_mul _
    have hgR : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ ∈ R.toValuationSubring := by rw [hg_eq]; exact mul_mem (R.algebraMap_mem' _) hinvR
    have hev : R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) = (p : AlgebraicClosure ℚ) * (R.evalAt (goodFamily Φ le))⁻¹ := by
      rw [hg_eq, evalAt_mul_D R hRrat (R.algebraMap_mem' _) hinvR, evalAt_algebraMap_D, hevinv]
    have hμlt : μ (R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹)) < 1 := by
      rw [hev, map_mul, map_inv₀, ← hmodp, hμtle]
      exact (mul_inv_lt_iff₀ (lt_of_le_of_lt (μ.nonneg _) hbig)).2 (lt_of_lt_of_eq hbig (one_mul _).symm)
    have hmem : R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) ∈ A := (hμA _).2 hμlt.le
    refine ⟨hmem, ?_⟩

    have hnu : ¬ IsUnit (⟨R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹), hmem⟩ : ↥A) := by
      intro hun
      have hinv := vs_inv_mem_of_isUnit_D hmem hun
      have h1 : μ (R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹))⁻¹ ≤ 1 := (hμA _).1 hinv
      rw [map_inv₀] at h1
      have h0 : R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) ≠ 0 := by
        rw [hev]; exact mul_ne_zero hp0 (inv_ne_zero htleR0)
      have hge : 1 ≤ μ (R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹)) :=
        (inv_le_one₀ (μ.pos h0)).1 h1
      exact absurd hge (not_le.mpr hμlt)
    rw [(IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hnu)]

    have hres1 : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹, hg⟩ = ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData le, huC⟩)⁻¹ := by
      rw [hgres]
      have : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hintZ i⟩ = 1 := by
        have e1 : (⟨goodFamilyZero Φ.toFamData i, hintZ i⟩ : (zeroChart Γ).integers) = 1 := Subtype.ext hv1
        rw [e1, map_one]
      rw [this, one_mul]
    have hordpos : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹, hg⟩) ≠ 0 := by
      rw [hres1, Place.ord_inv, hordu]; norm_num
    symm
    by_contra hne
    exact hordpos (ord_eq_zero_of_evalAt_ne_zero_D _ ((nodeSrc Γ e).mem_of_ord_nonneg hgres0 hordg) hne)
  ·
    have hi1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 hi
    have hni : hasseExp Φ.toFamData i = 1 :=
      le_antisymm (hasseExp_le_one_of_forall_widthOne p A hA Γ Δ Φ hw i) (one_le_hasseExp p A hA Γ Φ i hi1)
    have hti0 : goodFamily Φ i ≠ 0 := goodFamily_ne_zero' Φ i
    have hg_eq : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ = goodFamily Φ i * (goodFamily Φ le)⁻¹ := by
      rw [goodFamilyZero_eq_inv_mul' Φ i, hu_eq, hni, pow_one, mul_inv, inv_inv]
      field_simp
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e

    have hpole : ∀ Q ∈ (Δ.annIn e).dom, 0 ≤ Q.ord (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) := by
      intro Q hQ
      rw [hg_eq, Q.ord_mul hti0 (inv_ne_zero htle0), Place.ord_inv, hzf Q hQ, neg_zero, add_zero]
      exact (goodFamily_mem_of_ne_cuspInftyBar' Φ Q (ne_cuspInftyBar_of_mem_annIn_dom Γ Δ e Q hQ) i).1

    set C1 := chart Γ (tgt p e) with hC1
    have htleI : goodFamily Φ le ∈ C1.integers := hintI le
    have htleIres : C1.residue ⟨_, htleI⟩ ≠ 0 := hresI le
    have htleIinv : (goodFamily Φ le)⁻¹ ∈ C1.integers :=
      vs_inv_mem_of_isUnit_D htleI (chart_isUnit_of_residue_ne_zero_D C1 htleI htleIres)
    have hkey : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (1 : AlgebraicClosure ℚ))⁻¹ * (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹)
        = goodFamily Φ i * (goodFamily Φ le)⁻¹ := by rw [map_one, inv_one, hg_eq]; exact one_mul _
    have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (1 : AlgebraicClosure ℚ))⁻¹ * (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹)
        ∈ C1.integers := by rw [hkey]; exact mul_mem (hintI i) htleIinv
    have hres' : C1.residue ⟨_, hC'⟩ ≠ 0 := by
      have e1 : (⟨_, hC'⟩ : C1.integers) = ⟨goodFamily Φ i, hintI i⟩ * ⟨(goodFamily Φ le)⁻¹, htleIinv⟩ := Subtype.ext hkey
      rw [e1, map_mul, chart_residue_inv_D C1 htleI htleIres htleIinv]
      exact mul_ne_zero (hresI i) (inv_ne_zero htleIres)
    have hκ : μ (1 : AlgebraicClosure ℚ) = 1 := map_one μ
    obtain ⟨hmem, heq, -⟩ := AlgebraicCurve.Annulus.residue_evalAt_eq_evalAt_residue_of_isAttached_both_ends μ hμA
      (Δ.annIn e) (Δ.annOut e) hdom hmod hmod0 htwo
      (chart Γ (src p e)) (nodeSrc Γ e) (Δ.attached_src e) hdeg
      (chart Γ (tgt p e)) (nodeTgt Γ e) (Δ.attached_tgt e)
      (Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA)
      (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) hpole hg hgres0 1 hκ hC' hres' R hR
    exact ⟨hmem, heq⟩

end S_ModularCurve_MultCovering_residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne
end P2MW
export P2MW.S_ModularCurve_MultCovering_residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne (solution)
