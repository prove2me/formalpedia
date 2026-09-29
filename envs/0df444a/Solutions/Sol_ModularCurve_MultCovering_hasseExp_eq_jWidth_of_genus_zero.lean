-- Prove2me | solution 1 for ModularCurve.MultCovering.hasseExp_eq_jWidth_of_genus_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/93c3c476-61da-5474-96ad-1a5cce1cf5c0

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg P2MW.S_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq pow_mem_ssJSet_iff_of_perfectField isCurveOver_modularFunctionFieldC_of_perfectField"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_mem_toFinset ssValue_mem_ssJSet nodeSrc nodeTgt hasseExp goodFamilyZero FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero infChart_nodeData zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero"
p2m_open "ModularCurve.MultCovering ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg"

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
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq pow_mem_ssJSet_iff_of_perfectField isCurveOver_modularFunctionFieldC_of_perfectField"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_mem_toFinset ssValue_mem_ssJSet nodeSrc nodeTgt hasseExp goodFamilyZero FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero infChart_nodeData zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero"
p2m_open "ModularCurve.MultCovering ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg"
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
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq pow_mem_ssJSet_iff_of_perfectField isCurveOver_modularFunctionFieldC_of_perfectField"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_mem_toFinset ssValue_mem_ssJSet nodeSrc nodeTgt hasseExp goodFamilyZero FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero infChart_nodeData zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero"
namespace G0Aux
p2m_open "ModularCurve.MultCovering ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg"

open AlgebraicCurve IsLocalRing

theorem evalAt_sub_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem exists_eq_algebraMap_of_forall_ord_nonneg {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    [IsCurveOver k F] (v₀ : Place k F) (f : F) (hreg : ∀ v : Place k F, 0 ≤ v.ord f) :
    ∃ c : k, f = algebraMap k F c := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  haveI hPD : HasPrincipalDivisors k F := IsCurveOver.hasPrincipalDivisors
  have hrat : ∀ v : Place k F, v.IsRational := fun v =>
    isRational_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  have hfv : f ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hf0 (hreg v₀)
  set c : k := v₀.evalAt f with hc
  refine ⟨c, ?_⟩
  by_contra hne
  set g : F := f - algebraMap k F c with hg
  have hg0 : g ≠ 0 := sub_ne_zero.mpr hne

  have hgreg : ∀ v : Place k F, 0 ≤ v.ord g := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hf0 (hreg v)) (v.algebraMap_mem' c))

  have hgv : g ∈ v₀.toValuationSubring := sub_mem hfv (v₀.algebraMap_mem' c)
  have hev : v₀.evalAt g = 0 := by
    rw [hg, evalAt_sub_D v₀ (hrat v₀) hfv (v₀.algebraMap_mem' c), evalAt_algebraMap_D, hc, sub_self]
  have hpos : 0 < v₀.ord g := by
    refine lt_of_le_of_ne (hgreg v₀) fun h0 => ?_

    have hres0 : IsLocalRing.residue v₀.toValuationSubring ⟨g, hgv⟩ = 0 := by
      rw [← v₀.algebraMap_evalAt (hrat v₀) hgv, hev, map_zero]

    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v₀.toValuationSubring
    obtain ⟨u, hu⟩ := v₀.exists_unit_mul_zpow hg0 hπ
    rw [← h0, zpow_zero, mul_one] at hu
    have hgu : (⟨g, hgv⟩ : v₀.toValuationSubring) = (u : v₀.toValuationSubring) := Subtype.ext hu
    rw [hgu] at hres0
    exact (u.isUnit.map (IsLocalRing.residue v₀.toValuationSubring)).ne_zero hres0

  obtain ⟨D, hD, hdeg⟩ := hPD.exists_divisor g hg0
  have hall : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hgreg v
  have hv₀ : 0 < D v₀ := by rw [hD v₀]; exact hpos
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hv₀.ne'
  have hdegsum : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
    conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v (D v)
  have hdegpos : 0 < Divisor.degree D := by
    rw [hdegsum]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) := by
          rw [IsCurveOver.deg_eq_one_of_isAlgClosed v₀, Nat.cast_one, mul_one]; exact hv₀
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum (fun v _ => mul_nonneg (hall v) (Int.natCast_nonneg _)) hmem
  rw [hdeg] at hdegpos
  exact lt_irrefl 0 hdegpos

section Ctx
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

theorem mAnnuli_eq_one (Γ : ChartCtx p A) (hA : A.LiesOverPrime p) (Φ : FamCtx p 2) : mAnnuli p = 1 := by
  obtain ⟨hintT, -, P, hP, -, hPspan⟩ := Φ.t_inf A hA Γ

  have hcard : Fintype.card {l : Fin 2 // 1 ≤ (l : ℕ)} ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => Subtype.ext (Fin.ext (by
      have ha := a.2; have hb := b.2; have ha' := a.1.isLt; have hb' := b.1.isLt; omega))⟩
  have h1 : Module.finrank (IsLocalRing.ResidueField ↥A)
      ↥(Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin 2 // 1 ≤ (l : ℕ)} => P l)) ≤ 1 :=
    (finrank_range_le_card _).trans hcard
  rw [hPspan, (Polynomial.degreeLTEquiv (IsLocalRing.ResidueField ↥A) (mAnnuli p)).finrank_eq,
    Module.finrank_fin_fun] at h1

  have h2 := (hP 1 (by show 1 ≤ ((1 : Fin 2) : ℕ); decide)).1
  omega

theorem exists_of_mem_zeroChart_nodes (Γ : ChartCtx p A)
    (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    (hv : v ∈ (zeroChart Γ).nodes) :
    ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a = v := by
  have hv' : v ∈ Γ.Wn := hv
  rw [Γ.hWn] at hv'
  exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p _ v).mp hv'

theorem eq_nodeSrc_of_mem_zeroChart_nodes (Γ : ChartCtx p A) (hA : A.LiesOverPrime p) (Φ : FamCtx p 2)
    [PerfectField (IsLocalRing.ResidueField ↥A)] (e : Fin (mAnnuli p))
    (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    (hv : v ∈ (zeroChart Γ).nodes) : v = nodeSrc Γ e := by
  obtain ⟨a, ha, rfl⟩ := exists_of_mem_zeroChart_nodes Γ v hv
  have hm1 := mAnnuli_eq_one Γ hA Φ

  have hcard1 : Γ.hfin.toFinset.card = 1 := by rw [Γ.hcard, hm1]
  have huniq : ∀ b ∈ ssJSet p (IsLocalRing.ResidueField ↥A), b = ssValue Γ e := fun b hb =>
    Finset.card_le_one.mp hcard1.le b (Γ.hfin.mem_toFinset.mpr hb) _ (ssValue_mem_toFinset Γ e)
  have hpow : ssValue Γ e ^ p ∈ ssJSet p (IsLocalRing.ResidueField ↥A) :=
    (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p (ssValue Γ e)).mpr (ssValue_mem_ssJSet Γ e)
  rw [huniq a ha, ← huniq _ hpow]
  rfl

end Ctx

end ModularCurve.MultCovering.G0Aux

open ModularCurve.MultCovering.G0Aux in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (Φ : FamCtx p 2)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin 2 => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∀ e : Fin (mAnnuli p), hasseExp Φ.toFamData 1 = jWidth (ssValue Γ e) := by
  intro e
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  haveI hAC : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : IsCurveOver (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField _ 1

  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) < 1 := by
    have hmax : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(p : AlgebraicClosure ℚ), hpA⟩)).mp hA
    exact abv_lt_one_of_mem_maximalIdeal_D μ hμA hmax

  obtain ⟨hintI, hnd⟩ := infChart_nodeData p A hA Γ Φ
  obtain ⟨l₁, hl₁, hordl₁⟩ := (hnd e).2
  have hl₁eq : l₁ = 1 := Fin.ext (by have := l₁.isLt; simp only [Fin.val_one]; omega)
  subst hl₁eq

  obtain ⟨hintT, h0T, -⟩ := Φ.t_inf A hA Γ
  have hres0 : (infChart Γ).residue ⟨goodFamily Φ 0, hintI 0⟩ = 1 := h0T 0 rfl

  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨hintInf, hresInf⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZero, hresZero⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hmod0' : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn e).param * (Δ.annOut e).param = (Δ.annOut e).param * (Δ.annIn e).param from
      mul_comm _ _, htwo, hmod]

  have hpole : ∀ (l : Fin 2), ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l) := fun l Q hQ =>
    (goodFamily_mem_of_ne_cuspInftyBar' Φ Q (ne_cuspInftyBar_of_mem_annIn_dom Γ Δ e Q (hdom ▸ hQ)) l).1

  have key : ∀ l : Fin 2,
      -((nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩))
          ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) ∧
      ∀ R ∈ (Δ.annIn e).dom, 0 < R.ord (goodFamily Φ l) →
        1 - (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩)
          ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
    intro l
    have hscaled := goodFamilyZero_eq_inv_mul' Φ l
    set c' : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc'
    set h : modularFunctionFieldBar (1 * p) := goodFamily Φ l with hh
    have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
    have hc'A : c' ∈ A := pow_mem hpA _
    have hresinf : (infChart Γ).residue ⟨h, hintI l⟩ ≠ 0 := hresInf l
    have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * h ∈ (zeroChart Γ).integers := by
      rw [← hscaled]; exact hintZero l
    have e1 : (⟨_, hC'⟩ : (zeroChart Γ).integers) = ⟨_, hint l⟩ := Subtype.ext hscaled.symm
    have hres' : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0 := by rw [e1]; exact hresZero l
    obtain ⟨D, hD0, hDsupp, hDord, hdeg, -⟩ :=
      AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
        (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo'
        (infChart Γ) (nodeTgt Γ e) (Δ.attached_tgt e) (zeroChart Γ) (nodeSrc Γ e) (Δ.attached_src e)
        hwide h (hintI l) hresinf c' hc'0 hc'A hC' hres' (hpole l)
    rw [e1] at hdeg
    have hsum_nonneg : 0 ≤ D.sum (fun _ m => m) := by
      rw [Finsupp.sum]
      exact Finset.sum_nonneg fun Q _ => hD0 Q
    refine ⟨by linarith, fun R hR hRpos => ?_⟩
    have hDR : D R = R.ord h := hDord R (hdom ▸ hR)
    have hRsupp : R ∈ D.support := Finsupp.mem_support_iff.mpr (by rw [hDR]; exact hRpos.ne')
    have hle : D R ≤ D.sum (fun _ m => m) := by
      rw [Finsupp.sum]
      exact Finset.single_le_sum (fun Q _ => hD0 Q) hRsupp
    rw [hDR] at hle
    linarith

  have hzf : ∀ R ∈ (Δ.annIn e).dom, R.ord (goodFamily Φ 1) = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨R, hR, hne⟩ := hcon
    have hRpos : 0 < R.ord (goodFamily Φ 1) := lt_of_le_of_ne (hpole 1 R (hdom ▸ hR)) (Ne.symm hne)

    have hβ1 : 0 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 1, hint 1⟩) := by
      have := (key 1).2 R hR hRpos
      rw [hordl₁] at this
      linarith
    have hβ0 : 0 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩) := by
      have := (key 0).1
      rw [hres0, Place.ord_one] at this
      linarith

    obtain ⟨hintZ, hZ3⟩ := zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p A hA Γ Φ
    have hreg : ∀ l : Fin 2,
        0 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) →
        ∀ v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
          0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
      intro l hβ v
      by_cases hv : v ∈ (zeroChart Γ).nodes
      · rw [eq_nodeSrc_of_mem_zeroChart_nodes Γ hA Φ e v hv]; exact hβ
      · exact hZ3 l v hv
    obtain ⟨c₀, hc₀⟩ := exists_eq_algebraMap_of_forall_ord_nonneg (nodeSrc Γ e) _ (hreg 0 hβ0)
    obtain ⟨c₁, hc₁⟩ := exists_eq_algebraMap_of_forall_ord_nonneg (nodeSrc Γ e) _ (hreg 1 hβ1)

    have hpair : LinearIndependent (IsLocalRing.ResidueField ↥A)
        ![(zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩,
          (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 1, hint 1⟩] := by
      convert hLI using 1
      ext l
      fin_cases l <;> rfl
    rw [LinearIndependent.pair_iff] at hpair
    have hne0 : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩ ≠ 0 := hLI.ne_zero 0
    have hc₀0 : c₀ ≠ 0 := by
      intro h0; apply hne0; rw [hc₀, h0, map_zero]
    have hdep := hpair c₁ (-c₀) (by
      rw [hc₀, hc₁, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul, ← map_add,
        show c₁ * c₀ + -c₀ * c₁ = 0 by ring, map_zero])
    exact hc₀0 (neg_eq_zero.mp hdep.2)

  have hH3 := (ModularCurve.MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
    p A hA Γ Δ Φ e 1 (hintI 1) hordl₁ hzf μ hμA).1
  have hmodp : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  rw [hmodp, map_pow] at hH3
  exact pow_right_injective₀ hμp0 hμp1.ne hH3

end S_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero
end P2MW
export P2MW.S_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero (solution)
