-- Prove2me | solution 1 for ModularCurve.MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/89978177-4671-5c56-9259-7a64a9d0463d

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
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat_1728_mem_ssJSet_eleven
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg P2MW.S_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq isCurveOver_modularFunctionFieldC_of_perfectField zero_mem_ssJSet_iff ofNat_1728_mem_ssJSet_eleven ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx jBar mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_injective exists_ssValue_eq nodeSrc nodeTgt hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes"
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
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq isCurveOver_modularFunctionFieldC_of_perfectField zero_mem_ssJSet_iff ofNat_1728_mem_ssJSet_eleven ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx jBar mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_injective exists_ssValue_eq nodeSrc nodeTgt hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes"
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

namespace P11Poly
open Polynomial

theorem rootMultiplicity_add_rootMultiplicity_le_one {k : Type*} [Field k] [DecidableEq k]
    (P : Polynomial k) (hdeg : P.natDegree ≤ 1) {a b : k} (hab : a ≠ b) :
    P.rootMultiplicity a + P.rootMultiplicity b ≤ 1 := by
  classical
  rw [← Polynomial.count_roots P, ← Polynomial.count_roots P]
  have hcard : Multiset.card P.roots ≤ 1 := (Polynomial.card_roots' P).trans hdeg
  have h2 : Multiset.count a P.roots + Multiset.count b P.roots ≤ Multiset.card P.roots := by
    calc Multiset.count a P.roots + Multiset.count b P.roots
        = Multiset.card (P.roots.filter (· = a)) + Multiset.card (P.roots.filter (· = b)) := by
          rw [Multiset.count_eq_card_filter_eq, Multiset.count_eq_card_filter_eq]
          congr 1 <;> congr 1 <;> exact Multiset.filter_congr (fun x _ => by constructor <;> intro h <;> exact h.symm)
      _ = Multiset.card (P.roots.filter (· = a) + P.roots.filter (· = b)) := (Multiset.card_add _ _).symm
      _ ≤ Multiset.card P.roots := by
          apply Multiset.card_le_card
          rw [Multiset.le_iff_count]
          intro x
          rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
          by_cases hxa : x = a
          · subst hxa; simp [hab]
          · by_cases hxb : x = b
            · subst hxb; simp [hxa]
            · simp [hxa, hxb]
  omega

theorem rootMultiplicity_le_one {k : Type*} [Field k] (P : Polynomial k) (hdeg : P.natDegree ≤ 1)
    (a : k) : P.rootMultiplicity a ≤ 1 := by
  classical
  rw [← Polynomial.count_roots P]
  exact (Multiset.count_le_card a _).trans ((Polynomial.card_roots' P).trans hdeg)

theorem exists_smul_eq_of_isRoot {k : Type*} [Field k] (P Q : Polynomial k) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hP : P.natDegree ≤ 1) (hQ : Q.natDegree ≤ 1) (a : k) (hPa : P.IsRoot a) (hQa : Q.IsRoot a) :
    ∃ c : k, c ≠ 0 ∧ P = c • Q := by
  set p1 := P.coeff 1 with hp1
  set p0 := P.coeff 0 with hp0
  set q1 := Q.coeff 1 with hq1
  set q0 := Q.coeff 0 with hq0
  have eP : P = C p1 * X + C p0 := Polynomial.eq_X_add_C_of_natDegree_le_one hP
  have eQ : Q = C q1 * X + C q0 := Polynomial.eq_X_add_C_of_natDegree_le_one hQ

  have hP1 : p1 ≠ 0 := by
    intro h0
    rw [h0, C_0, zero_mul, zero_add] at eP
    rw [eP, IsRoot, eval_C] at hPa
    apply hP0; rw [eP, hPa, C_0]
  have hQ1 : q1 ≠ 0 := by
    intro h0
    rw [h0, C_0, zero_mul, zero_add] at eQ
    rw [eQ, IsRoot, eval_C] at hQa
    apply hQ0; rw [eQ, hQa, C_0]

  have hP0' : p0 = -(p1 * a) := by
    rw [eP, IsRoot, eval_add, eval_mul, eval_C, eval_X, eval_C] at hPa; linear_combination hPa
  have hQ0' : q0 = -(q1 * a) := by
    rw [eQ, IsRoot, eval_add, eval_mul, eval_C, eval_X, eval_C] at hQa; linear_combination hQa
  refine ⟨p1 * q1⁻¹, mul_ne_zero hP1 (inv_ne_zero hQ1), ?_⟩
  rw [eP, eQ, hP0', hQ0', smul_add, smul_eq_C_mul, smul_eq_C_mul]
  have h1 : C (p1 * q1⁻¹) * (C q1 * X) = C p1 * X := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel_right₀ hQ1]
  have h2 : C (p1 * q1⁻¹) * C (-(q1 * a)) = C (-(p1 * a)) := by
    rw [← C_mul]; congr 1; field_simp
  rw [h1, h2]

end P11Poly

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq isCurveOver_modularFunctionFieldC_of_perfectField zero_mem_ssJSet_iff ofNat_1728_mem_ssJSet_eleven ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx jBar mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_injective exists_ssValue_eq nodeSrc nodeTgt hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes"
namespace P11Aux
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

theorem ord_pos_of_evalAt_eq_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.evalAt f = 0) :
    0 < v.ord f := by
  refine lt_of_le_of_ne (v.ord_nonneg_of_mem hf) fun h0 => ?_
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
    rw [← v.algebraMap_evalAt hv hf, h, map_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  rw [← h0, zpow_zero, mul_one] at hu
  have hgu : (⟨f, hf⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
  rw [hgu] at hres0
  exact (u.isUnit.map (IsLocalRing.residue v.toValuationSubring)).ne_zero hres0

section Ctx
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

theorem exists_of_mem_zeroChart_nodes (Γ : ChartCtx p A)
    (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    (hv : v ∈ (zeroChart Γ).nodes) :
    ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a = v := by
  have hv' : v ∈ Γ.Wn := hv
  rw [Γ.hWn] at hv'
  exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p _ v).mp hv'

end Ctx

theorem sum_ord_le_zero_of_forall_not_mem_ord_nonneg {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    [IsCurveOver k F] (f : F) (hf0 : f ≠ 0) (S : Finset (Place k F))
    (hreg : ∀ v : Place k F, v ∉ S → 0 ≤ v.ord f) :
    ∑ v ∈ S, v.ord f ≤ 0 := by
  classical
  haveI hPD : HasPrincipalDivisors k F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨D, hD, hdeg⟩ := hPD.exists_divisor f hf0
  have hdegsum : Divisor.degree D = ∑ v ∈ D.support, D v := by
    conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Divisor.degree_single v (D v), IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one, mul_one]
  have h1 : ∑ v ∈ S, v.ord f = ∑ v ∈ S ∩ D.support, D v := by
    rw [← Finset.sum_inter_add_sum_sdiff S D.support (fun v => v.ord f)]
    have hz : ∑ v ∈ S \ D.support, v.ord f = 0 :=
      Finset.sum_eq_zero fun v hv => by
        rw [← hD v]; exact Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hv).2
    rw [hz, add_zero]
    exact Finset.sum_congr rfl fun v _ => (hD v).symm
  have h2 : ∑ v ∈ D.support, D v = ∑ v ∈ D.support ∩ S, D v + ∑ v ∈ D.support \ S, D v :=
    (Finset.sum_inter_add_sum_sdiff D.support S (fun v => D v)).symm
  have h3 : 0 ≤ ∑ v ∈ D.support \ S, D v :=
    Finset.sum_nonneg fun v hv => by rw [hD v]; exact hreg v (Finset.mem_sdiff.mp hv).2
  rw [h1, Finset.inter_comm]
  linarith [hdeg, hdegsum]

theorem not_linearIndependent_of_simple_pole {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    [IsCurveOver k F] (v : Place k F) (u₀ u₁ u₂ : F) (c₀ : k) (hc₀ : c₀ ≠ 0) (hu₀ : u₀ = algebraMap k F c₀)
    (hu₁ : v.ord u₁ = -1) (hu₂ : v.ord u₂ = -1)
    (hr₁ : ∀ w : Place k F, w ≠ v → 0 ≤ w.ord u₁) (hr₂ : ∀ w : Place k F, w ≠ v → 0 ≤ w.ord u₂) :
    ¬ LinearIndependent k ![u₀, u₁, u₂] := by
  classical
  intro hLI
  rw [Fintype.linearIndependent_iff] at hLI
  have hrat : ∀ w : Place k F, w.IsRational := fun w =>
    isRational_of_deg_eq_one w (IsCurveOver.deg_eq_one_of_isAlgClosed w)
  have hu₁0 : u₁ ≠ 0 := by intro h; rw [h, Place.ord_zero] at hu₁; norm_num at hu₁
  have hu₂0 : u₂ ≠ 0 := by intro h; rw [h, Place.ord_zero] at hu₂; norm_num at hu₂

  set ρ : F := u₁ * u₂⁻¹ with hρ
  have hρ0 : ρ ≠ 0 := mul_ne_zero hu₁0 (inv_ne_zero hu₂0)
  have hρord : v.ord ρ = 0 := by
    rw [hρ, v.ord_mul hu₁0 (inv_ne_zero hu₂0), Place.ord_inv, hu₁, hu₂]; ring
  have hρv : ρ ∈ v.toValuationSubring := v.mem_of_ord_nonneg hρ0 hρord.symm.le
  set d : k := v.evalAt ρ with hd
  have hdv : algebraMap k F d ∈ v.toValuationSubring := v.algebraMap_mem' d

  set h : F := u₁ - algebraMap k F d * u₂ with hh
  by_cases hh0 : h = 0
  · have hsum : ∑ i, (![0, 1, -d] i) • (![u₀, u₁, u₂] i) = 0 := by
      rw [Fin.sum_univ_three]
      show (0 : k) • u₀ + (1 : k) • u₁ + (-d) • u₂ = 0
      rw [zero_smul, zero_add, one_smul, neg_smul, Algebra.smul_def, ← sub_eq_add_neg]; exact hh0
    have := hLI ![0, 1, -d] hsum 1
    simp at this

  have hfac : h = u₂ * (ρ - algebraMap k F d) := by
    rw [hh, hρ, mul_sub, ← mul_assoc, mul_comm u₂ u₁, mul_assoc, mul_inv_cancel₀ hu₂0, mul_one, mul_comm]
  have hρd0 : ρ - algebraMap k F d ≠ 0 := by
    intro h0; apply hh0; rw [hfac, h0, mul_zero]
  have hρdv : ρ - algebraMap k F d ∈ v.toValuationSubring := sub_mem hρv hdv
  have hev : v.evalAt (ρ - algebraMap k F d) = 0 := by
    rw [evalAt_sub_D v (hrat v) hρv hdv, evalAt_algebraMap_D, hd, sub_self]
  have hpos : 0 < v.ord (ρ - algebraMap k F d) := ord_pos_of_evalAt_eq_zero_D v (hrat v) hρdv hρd0 hev
  have hreg : ∀ w : Place k F, 0 ≤ w.ord h := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hfac, w.ord_mul hu₂0 hρd0, hu₂]; omega
    · exact w.ord_nonneg_of_mem (sub_mem (w.mem_of_ord_nonneg hu₁0 (hr₁ w hw))
        (mul_mem (w.algebraMap_mem' d) (w.mem_of_ord_nonneg hu₂0 (hr₂ w hw))))

  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_ord_nonneg v h hreg
  have hsum : ∑ i, (![-(c * c₀⁻¹), 1, -d] i) • (![u₀, u₁, u₂] i) = 0 := by
    rw [Fin.sum_univ_three]
    show (-(c * c₀⁻¹)) • u₀ + (1 : k) • u₁ + (-d) • u₂ = 0
    rw [hu₀, one_smul, neg_smul, neg_smul, Algebra.smul_def, Algebra.smul_def, ← map_mul,
      show c * c₀⁻¹ * c₀ = c by field_simp, ← hc, hh]
    ring
  have := hLI ![-(c * c₀⁻¹), 1, -d] hsum 1
  simp at this

end ModularCurve.MultCovering.P11Aux

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar ssJSet PlaceSpecialization.jFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq isCurveOver_modularFunctionFieldC_of_perfectField zero_mem_ssJSet_iff ofNat_1728_mem_ssJSet_eleven ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx jBar mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart ssValue ssValue_injective exists_ssValue_eq nodeSrc nodeTgt hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes"
p2m_open "ModularCurve.MultCovering ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg"

open AlgebraicCurve IsLocalRing

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem tube_law (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (e : Fin (mAnnuli p)) (l : Fin r) :
    ∃ N : ℤ, 0 ≤ N ∧
      N = (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩)
          + (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) ∧
      (N = 0 → (hasseExp Φ.toFamData l : ℤ)
          + (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
              * (jWidth (ssValue Γ e) : ℤ) = 0) ∧
      (1 ≤ N →
        (hasseExp Φ.toFamData l : ℤ)
          + (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
              * (jWidth (ssValue Γ e) : ℤ) < N * (jWidth (ssValue Γ e) : ℤ) ∧
        0 < (hasseExp Φ.toFamData l : ℤ)
          + (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
              * (jWidth (ssValue Γ e) : ℤ)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) < 1 := by
    have hmax : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(p : AlgebraicClosure ℚ), hpA⟩)).mp hA
    exact abv_lt_one_of_mem_maximalIdeal_D μ hμA hmax
  have hL : Real.log (μ (p : AlgebraicClosure ℚ)) < 0 := Real.log_neg hμp0 hμp1

  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨hintInf, hresInf⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZero, hresZero⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hmod0' : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn e).param * (Δ.annOut e).param = (Δ.annOut e).param * (Δ.annIn e).param from
      mul_comm _ _, htwo, hmod]
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l) := fun Q hQ =>
    (goodFamily_mem_of_ne_cuspInftyBar' Φ Q (ne_cuspInftyBar_of_mem_annIn_dom Γ Δ e Q (hdom ▸ hQ)) l).1

  have hscaled := goodFamilyZero_eq_inv_mul' Φ l
  set n : ℕ := hasseExp Φ.toFamData l with hn
  set w : ℕ := jWidth (ssValue Γ e) with hw
  set c' : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ n with hc'
  set h : modularFunctionFieldBar (1 * p) := goodFamily Φ l with hh
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem hpA _
  have hresinf : (infChart Γ).residue ⟨h, hintI l⟩ ≠ 0 := by
    have e0 : (⟨h, hintI l⟩ : (infChart Γ).integers) = ⟨_, hintInf l⟩ := Subtype.ext rfl
    rw [e0]; exact hresInf l
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * h ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hintZero l
  have e1 : (⟨_, hC'⟩ : (zeroChart Γ).integers) = ⟨_, hint l⟩ := Subtype.ext hscaled.symm
  have hres' : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0 := by
    rw [e1]
    have e2 : (⟨_, hint l⟩ : (zeroChart Γ).integers) = ⟨_, hintZero l⟩ := Subtype.ext rfl
    rw [e2]; exact hresZero l
  obtain ⟨D, hD0, hDsupp, hDord, hdeg, hsum⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo'
      (infChart Γ) (nodeTgt Γ e) (Δ.attached_tgt e) (zeroChart Γ) (nodeSrc Γ e) (Δ.attached_src e)
      hwide h (hintI l) hresinf c' hc'0 hc'A hC' hres' hpole
  rw [e1] at hdeg hsum
  set β : ℤ := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) with hβ

  have hmodp : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ w := by
    rw [hmod]
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  have hlogc : Real.log (μ c') = (n : ℝ) * Real.log (μ (p : AlgebraicClosure ℚ)) := by
    rw [hc', map_pow, Real.log_pow]
  have hlogm : Real.log (μ ((Δ.annOut e).modulus : AlgebraicClosure ℚ)) = (w : ℝ) * Real.log (μ (p : AlgebraicClosure ℚ)) := by
    rw [hmodp, map_pow, Real.log_pow]
  rw [hlogc, hlogm] at hsum

  have hQ : ∀ Q ∈ D.support,
      (w : ℝ) * Real.log (μ (p : AlgebraicClosure ℚ)) < Real.log (μ (Q.evalAt (Δ.annOut e).param)) ∧
      Real.log (μ (Q.evalAt (Δ.annOut e).param)) < 0 ∧ (1 : ℤ) ≤ D Q := by
    intro Q hQs
    have hQd : Q ∈ (Δ.annOut e).dom := hDsupp Q (Finsupp.mem_support_iff.mp hQs)
    obtain ⟨-, -, ⟨hzA, hz𝔪⟩, hz0, m, hm𝔪, hmz⟩ := (Δ.annOut e).mem_dom Q hQd
    have hz1 : μ (Q.evalAt (Δ.annOut e).param) < 1 := abv_lt_one_of_mem_maximalIdeal_D μ hμA hz𝔪
    have hzpos : 0 < μ (Q.evalAt (Δ.annOut e).param) := μ.pos hz0
    have hm1 : μ (m : AlgebraicClosure ℚ) < 1 := abv_lt_one_of_mem_maximalIdeal_D μ hμA hm𝔪
    have hmodlt : μ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) < μ (Q.evalAt (Δ.annOut e).param) := by
      rw [hmz, map_mul]
      calc μ (Q.evalAt (Δ.annOut e).param) * μ (m : AlgebraicClosure ℚ)
          < μ (Q.evalAt (Δ.annOut e).param) * 1 := mul_lt_mul_of_pos_left hm1 hzpos
        _ = _ := mul_one _
    refine ⟨?_, Real.log_neg hzpos hz1, ?_⟩
    · rw [← hlogm]; exact Real.log_lt_log (μ.pos hmod0') hmodlt
    · have := hD0 Q; have h2 := Finsupp.mem_support_iff.mp hQs; omega

  set N : ℤ := D.sum (fun _ m => m) with hN
  have hNsum : N = ∑ Q ∈ D.support, D Q := by rw [hN, Finsupp.sum]
  have hSsum : (D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt (Δ.annOut e).param)))
      = ∑ Q ∈ D.support, (D Q : ℝ) * Real.log (μ (Q.evalAt (Δ.annOut e).param)) := by rw [Finsupp.sum]
  rw [hSsum] at hsum
  have hN0 : 0 ≤ N := by rw [hNsum]; exact Finset.sum_nonneg fun Q _ => hD0 Q
  refine ⟨N, hN0, hdeg, fun hN00 => ?_, fun hN1 => ?_⟩
  ·
    have hsupp : D.support = ∅ := by
      by_contra hne
      obtain ⟨Q, hQs⟩ := Finset.nonempty_of_ne_empty hne
      have h1 := (hQ Q hQs).2.2
      have : (1 : ℤ) ≤ ∑ Q ∈ D.support, D Q :=
        le_trans h1 (Finset.single_le_sum (fun Q _ => hD0 Q) hQs)
      rw [← hNsum, hN00] at this; exact absurd this (by norm_num)
    rw [hsupp, Finset.sum_empty] at hsum
    have hreal : ((n : ℝ) + (β : ℝ) * (w : ℝ)) * Real.log (μ (p : AlgebraicClosure ℚ)) = 0 := by linarith
    have h2 : (n : ℝ) + (β : ℝ) * (w : ℝ) = 0 := by
      rcases mul_eq_zero.mp hreal with h | h
      · exact h
      · exact absurd h hL.ne
    exact_mod_cast h2
  ·
    have hne : D.support.Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      rw [hNsum, hem, Finset.sum_empty] at hN1; exact absurd hN1 (by norm_num)
    have hlt0 : ∑ Q ∈ D.support, (D Q : ℝ) * Real.log (μ (Q.evalAt (Δ.annOut e).param)) < 0 := by
      apply Finset.sum_neg (fun Q hQs => ?_) hne
      have h1 := hQ Q hQs
      have hDQ : (0 : ℝ) < (D Q : ℝ) := by exact_mod_cast (show (0:ℤ) < D Q by linarith [h1.2.2])
      exact mul_neg_of_pos_of_neg hDQ h1.2.1
    have hgt : ∑ Q ∈ D.support, (D Q : ℝ) * ((w : ℝ) * Real.log (μ (p : AlgebraicClosure ℚ)))
        < ∑ Q ∈ D.support, (D Q : ℝ) * Real.log (μ (Q.evalAt (Δ.annOut e).param)) := by
      apply Finset.sum_lt_sum_of_nonempty hne
      intro Q hQs
      have h1 := hQ Q hQs
      have hDQ : (0 : ℝ) < (D Q : ℝ) := by exact_mod_cast (show (0:ℤ) < D Q by linarith [h1.2.2])
      exact mul_lt_mul_of_pos_left h1.1 hDQ
    rw [← Finset.sum_mul] at hgt
    have hNR : (∑ Q ∈ D.support, (D Q : ℝ)) = (N : ℝ) := by rw [hNsum]; norm_cast
    rw [hNR] at hgt

    rw [hsum] at hgt hlt0
    set L := Real.log (μ (p : AlgebraicClosure ℚ)) with hLdef
    set X : ℝ := (n : ℝ) + (β : ℝ) * (w : ℝ) with hX
    have hgt' : ((N : ℝ) * (w : ℝ)) * L < X * L := by rw [hX]; linarith [hgt]
    have hlt0' : X * L < 0 := by rw [hX]; linarith [hlt0]
    have h1 : X < (N : ℝ) * (w : ℝ) := (mul_lt_mul_right_of_neg hL).mp hgt'
    have h2 : 0 < X := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hcon, hL]
    rw [hX] at h1 h2
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2

end ModularCurve.MultCovering

open ModularCurve.MultCovering.P11Aux P11Poly in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime] (hp11 : p = 11)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (Φ : FamCtx p 3)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin 3 => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (l₂ l₃ : Fin 3),
      l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
      hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 3 ∧
      ∀ e : Fin (mAnnuli p),
        (ssValue Γ e = 1728 →
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩) = 1 ∧
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint l₂⟩) = -1 ∧
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩) = 2) ∧
        (ssValue Γ e = 0 →
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩) = 1 ∧
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₃, hint l₃⟩) = -1) := by
  subst hp11

  haveI hAC : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : IsCurveOver (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField _ 1

  have hm2 : mAnnuli 11 = 2 := by decide
  have h1728 : ((1728 : ℕ) : (IsLocalRing.ResidueField ↥A)) = (1728 : (IsLocalRing.ResidueField ↥A)) := by norm_cast
  have h1728ne : (1728 : (IsLocalRing.ResidueField ↥A)) ≠ 0 := by
    rw [show (1728 : (IsLocalRing.ResidueField ↥A)) = ((1728 : ℕ) : (IsLocalRing.ResidueField ↥A)) by norm_cast, show (1728 : ℕ) = 11 * 157 + 1 by norm_num,
      Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero (IsLocalRing.ResidueField ↥A) 11, zero_mul, zero_add, Nat.cast_one]
    exact one_ne_zero

  have h0ss : (0 : (IsLocalRing.ResidueField ↥A)) ∈ ssJSet 11 (IsLocalRing.ResidueField ↥A) := (ModularCurve.zero_mem_ssJSet_iff 11 (by norm_num) (IsLocalRing.ResidueField ↥A)).2 (by norm_num)
  have h1728ss : (1728 : (IsLocalRing.ResidueField ↥A)) ∈ ssJSet 11 (IsLocalRing.ResidueField ↥A) := ModularCurve.ofNat_1728_mem_ssJSet_eleven (IsLocalRing.ResidueField ↥A)
  obtain ⟨e₀, he₀⟩ := exists_ssValue_eq Γ 0 h0ss
  obtain ⟨e₁, he₁⟩ := exists_ssValue_eq Γ 1728 h1728ss
  have hne : e₀ ≠ e₁ := by
    intro h; apply h1728ne; rw [← he₁, ← h, he₀]
  have hall : ∀ e : Fin (mAnnuli 11), e = e₀ ∨ e = e₁ := by
    intro e
    by_cases h0 : e = e₀
    · exact Or.inl h0
    · right
      apply Fin.ext
      have h0' : (e : ℕ) ≠ e₀ := fun h => h0 (Fin.ext h)
      have hne' : (e₀ : ℕ) ≠ e₁ := fun h => hne (Fin.ext h)
      have h1 : (e : ℕ) < 2 := lt_of_lt_of_eq e.isLt hm2
      have h2 : (e₀ : ℕ) < 2 := lt_of_lt_of_eq e₀.isLt hm2
      have h3 : (e₁ : ℕ) < 2 := lt_of_lt_of_eq e₁.isLt hm2
      omega
  have hval : ∀ e : Fin (mAnnuli 11), ssValue Γ e = 0 ∨ ssValue Γ e = 1728 := by
    intro e; rcases hall e with rfl | rfl
    · exact Or.inl he₀
    · exact Or.inr he₁

  have hw0 : jWidth (ssValue Γ e₀) = 3 := by rw [he₀]; exact jWidth_of_eq_zero rfl
  have hw1 : jWidth (ssValue Γ e₁) = 2 := by rw [he₁]; exact jWidth_of_eq_1728 rfl h1728ne

  have hfrob : ∀ e : Fin (mAnnuli 11), ssValue Γ e ^ 11 = ssValue Γ e := by
    intro e; rcases hval e with h | h
    · rw [h]; norm_num
    · rw [h]
      have h2 := map_natCast (frobenius (IsLocalRing.ResidueField ↥A) 11) 1728
      rw [frobenius_def] at h2
      exact_mod_cast h2
  have hnodeSrc : ∀ e : Fin (mAnnuli 11), nodeSrc Γ e = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e) := by
    intro e
    show charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ 11) = _
    rw [hfrob e]
  have hnodeTgt : ∀ e : Fin (mAnnuli 11), nodeTgt Γ e = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e) := fun e => rfl

  have hjsub := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (IsLocalRing.ResidueField ↥A)
  have hplaces : charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (0 : (IsLocalRing.ResidueField ↥A)) ≠ charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) 1728 := by
    intro h
    have h1 := hjsub (0 : (IsLocalRing.ResidueField ↥A)) 0
    have h2 := hjsub (1728 : (IsLocalRing.ResidueField ↥A)) 0
    rw [if_pos rfl] at h1
    rw [if_neg h1728ne.symm, ← h, h1] at h2
    exact one_ne_zero h2
  have hsrcne : nodeSrc Γ e₀ ≠ nodeSrc Γ e₁ := by
    rw [hnodeSrc, hnodeSrc, he₀, he₁]; exact hplaces

  have hnodes : ∀ v ∈ (zeroChart Γ).nodes, v = nodeSrc Γ e₀ ∨ v = nodeSrc Γ e₁ := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_zeroChart_nodes Γ v hv
    obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
    rcases hall e with rfl | rfl
    · left; rw [hnodeSrc, he]
    · right; rw [hnodeSrc, he]

  obtain ⟨hintT, h0T, P, hP, hPli, -⟩ := Φ.t_inf A hA Γ

  have hssord : ∀ e : Fin (mAnnuli 11), (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ) = 1 := by
    intro e
    have huniv : (Finset.univ : Finset (Fin (mAnnuli 11))) = {e₀, e₁} := by
      ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]; exact hall x
    have hprod : ssPolyBar Γ = (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e₀)) * (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e₁)) := by
      show (∏ e' : Fin (mAnnuli 11), (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e'))) = _
      rw [huniv, Finset.prod_pair hne]
    have hf0 : ∀ e' : Fin (mAnnuli 11), (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (ssValue Γ e')) ≠ 0 := by
      intro e' h0
      have := hjsub (ssValue Γ e') (ssValue Γ e')
      rw [if_pos rfl] at this
      change (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e')).ord
        (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e')) = 1 at this
      rw [h0, Place.ord_zero] at this; exact zero_ne_one this
    rw [hprod, (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord_mul (hf0 e₀) (hf0 e₁)]
    have hA0 := hjsub (ssValue Γ e) (ssValue Γ e₀)
    have hA1 := hjsub (ssValue Γ e) (ssValue Γ e₁)
    change (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord (jBar (IsLocalRing.ResidueField ↥A) - _) = _ at hA0
    change (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord (jBar (IsLocalRing.ResidueField ↥A) - _) = _ at hA1
    rw [hA0, hA1]
    have hinj := ssValue_injective Γ
    rcases hall e with he | he
    · rw [he]
      have h2 : ¬ (ssValue Γ e₁ = ssValue Γ e₀) := fun h => hne (hinj h).symm
      simp [h2]
    · rw [he]
      have h2 : ¬ (ssValue Γ e₀ = ssValue Γ e₁) := fun h => hne (hinj h)
      simp [h2]

  obtain ⟨hintInf, hresInf⟩ := infChart_goodFamily_residue_ne_zero 11 A hA Γ Φ
  obtain ⟨hintZero, hresZero⟩ := zeroChart_residue_goodFamilyZero_ne_zero 11 A hA Γ Φ
  have hresT : ∀ l : Fin 3, (infChart Γ).residue ⟨goodFamily Φ l, hintT l⟩ ≠ 0 := by
    intro l
    have e0 : (⟨goodFamily Φ l, hintT l⟩ : (infChart Γ).integers) = ⟨_, hintInf l⟩ := Subtype.ext rfl
    rw [e0]; exact hresInf l
  have hresZ : ∀ l : Fin 3, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ ≠ 0 := by
    intro l
    have e0 : (⟨goodFamilyZero Φ.toFamData l, hint l⟩ : (zeroChart Γ).integers) = ⟨_, hintZero l⟩ := Subtype.ext rfl
    rw [e0]; exact hresZero l

  have hdegP : ∀ (l : Fin 3), 1 ≤ (l : ℕ) → (P l).natDegree ≤ 1 := by
    intro l hl; have := (hP l hl).1; rw [hm2] at this; omega
  have hα : ∀ (l : Fin 3), 1 ≤ (l : ℕ) → ∀ e : Fin (mAnnuli 11),
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintT l⟩) = 1 + ((P l).rootMultiplicity (ssValue Γ e) : ℤ) := by
    intro l hl e
    have hres := (hP l hl).2
    have hne0 := hresT l
    change (infChart Γ).residue ⟨Φ.t l, hintT l⟩ ≠ 0 at hne0
    rw [hres] at hne0
    have hss0 : ssPolyBar Γ ≠ 0 := left_ne_zero_of_mul hne0
    have haev0 : Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) ≠ 0 := right_ne_zero_of_mul hne0
    show (nodeTgt Γ e).ord ((infChart Γ).residue ⟨Φ.t l, hintT l⟩) = _
    rw [hres, hnodeTgt, (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord_mul hss0 haev0, hssord e]
    congr 1
    exact ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity (IsLocalRing.ResidueField ↥A) (ssValue Γ e) (P l)

  obtain ⟨hintZ, hZ3⟩ := zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes 11 A hA Γ Φ
  have hZ3' : ∀ (l : Fin 3) (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)), v ∉ (zeroChart Γ).nodes →
      0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
    intro l v hv
    have e0 : (⟨goodFamilyZero Φ.toFamData l, hint l⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext rfl
    rw [e0]; exact hZ3 l v hv

  have hoff : ∀ (l : Fin 3) (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)), v ≠ nodeSrc Γ e₀ → v ≠ nodeSrc Γ e₁ →
      0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
    intro l v h0 h1
    apply hZ3' l v
    intro hv
    rcases hnodes v hv with h | h
    · exact h0 h
    · exact h1 h
  classical
  have hdegree : ∀ l : Fin 3,
      (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
        + (nodeSrc Γ e₁).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) ≤ 0 := by
    intro l
    have := sum_ord_le_zero_of_forall_not_mem_ord_nonneg
      ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) (hresZ l) {nodeSrc Γ e₀, nodeSrc Γ e₁}
      (fun v hv => by
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
        exact hoff l v hv.1 hv.2)
    rwa [Finset.sum_pair hsrcne] at this

  have hres0T : (infChart Γ).residue ⟨goodFamily Φ 0, hintT 0⟩ = 1 := h0T 0 rfl
  have hβ0 : ∀ e : Fin (mAnnuli 11), 0 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩) := by
    intro e
    obtain ⟨N, hN0, hNeq, -, -⟩ := tube_law 11 A hA Γ Δ Φ hintT hint μ hμA e 0
    rw [hres0T, Place.ord_one] at hNeq
    linarith
  have hreg0 : ∀ v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
      0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩) := by
    intro v
    by_cases h0 : v = nodeSrc Γ e₀
    · rw [h0]; exact hβ0 e₀
    by_cases h1 : v = nodeSrc Γ e₁
    · rw [h1]; exact hβ0 e₁
    exact hoff 0 v h0 h1
  obtain ⟨c₀, hc₀⟩ := exists_eq_algebraMap_of_forall_ord_nonneg (nodeSrc Γ e₀) _ hreg0
  have hc₀0 : c₀ ≠ 0 := by
    intro h0; apply hresZ 0; rw [hc₀, h0, map_zero]

  have hnonconst : ∀ (l : Fin 3), 1 ≤ (l : ℕ) →
      ¬ (0 ≤ (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) ∧
         0 ≤ (nodeSrc Γ e₁).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) := by
    intro l hl hboth
    have hregl : ∀ v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
      intro v
      by_cases h0 : v = nodeSrc Γ e₀
      · rw [h0]; exact hboth.1
      by_cases h1 : v = nodeSrc Γ e₁
      · rw [h1]; exact hboth.2
      exact hoff l v h0 h1
    obtain ⟨c₁, hc₁⟩ := exists_eq_algebraMap_of_forall_ord_nonneg (nodeSrc Γ e₀) _ hregl
    have hl0 : (0 : Fin 3) ≠ l := by intro h; rw [← h] at hl; exact absurd hl (by decide)
    have hpair : LinearIndependent (IsLocalRing.ResidueField ↥A)
        ![(zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩,
          (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩] := by
      have hinj : Function.Injective (![0, l] : Fin 2 → Fin 3) := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [hl0, hl0.symm]
      convert hLI.comp _ hinj using 1
      ext i; fin_cases i <;> rfl
    rw [LinearIndependent.pair_iff] at hpair
    have hdep := hpair c₁ (-c₀) (by
      rw [hc₀, hc₁, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul, ← map_add,
        show c₁ * c₀ + -c₀ * c₁ = 0 by ring, map_zero])
    exact hc₀0 (neg_eq_zero.mp hdep.2)

  have hP01 : ssValue Γ e₀ ≠ ssValue Γ e₁ := by rw [he₀, he₁]; exact h1728ne.symm
  have member : ∀ (l : Fin 3), 1 ≤ (l : ℕ) →
      ((P l).rootMultiplicity (ssValue Γ e₁) = 1 →
          hasseExp Φ.toFamData l = 3 ∧
          (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) = -1 ∧
          (P l).rootMultiplicity (ssValue Γ e₀) = 0) ∧
      ((P l).rootMultiplicity (ssValue Γ e₁) = 0 →
          hasseExp Φ.toFamData l = 2 ∧
          (nodeSrc Γ e₁).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) = -1 ∧
          0 ≤ (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) ∧
      (P l).rootMultiplicity (ssValue Γ e₁) ≤ 1 := by
    intro l hl
    have hmm := rootMultiplicity_add_rootMultiplicity_le_one (P l) (hdegP l hl) hP01
    have hα0 := hα l hl e₀
    have hα1 := hα l hl e₁
    obtain ⟨N₀, hN₀0, hN₀eq, hN₀z, hN₀p⟩ := tube_law 11 A hA Γ Δ Φ hintT hint μ hμA e₀ l
    obtain ⟨N₁, hN₁0, hN₁eq, hN₁z, hN₁p⟩ := tube_law 11 A hA Γ Δ Φ hintT hint μ hμA e₁ l
    rw [hw0] at hN₀z hN₀p
    rw [hw1] at hN₁z hN₁p
    rw [hα0] at hN₀eq
    rw [hα1] at hN₁eq
    have hdg := hdegree l
    have hnc := hnonconst l hl
    push_cast at hN₀z hN₀p hN₁z hN₁p
    rcases eq_or_lt_of_le hN₀0 with hz0 | hp0 <;> rcases eq_or_lt_of_le hN₁0 with hz1 | hp1
    · have f0 := hN₀z hz0.symm; have f1 := hN₁z hz1.symm
      refine ⟨fun h1 => ⟨?_, ?_, ?_⟩, fun h0 => ⟨?_, ?_, ?_⟩, ?_⟩ <;> omega
    · have f0 := hN₀z hz0.symm; obtain ⟨f1, f1'⟩ := hN₁p (by omega)
      refine ⟨fun h1 => ⟨?_, ?_, ?_⟩, fun h0 => ⟨?_, ?_, ?_⟩, ?_⟩ <;> omega
    · obtain ⟨f0, f0'⟩ := hN₀p (by omega); have f1 := hN₁z hz1.symm
      refine ⟨fun h1 => ⟨?_, ?_, ?_⟩, fun h0 => ⟨?_, ?_, ?_⟩, ?_⟩ <;> omega
    · obtain ⟨f0, f0'⟩ := hN₀p (by omega); obtain ⟨f1, f1'⟩ := hN₁p (by omega)
      refine ⟨fun h1 => ⟨?_, ?_, ?_⟩, fun h0 => ⟨?_, ?_, ?_⟩, ?_⟩ <;> omega

  have hm1 := member 1 (by decide)
  have hm2' := member 2 (by decide)
  have hnotboth0 : ¬ ((P 1).rootMultiplicity (ssValue Γ e₁) = 0 ∧ (P 2).rootMultiplicity (ssValue Γ e₁) = 0) := by
    rintro ⟨h10, h20⟩
    obtain ⟨-, hb1, hb0⟩ := hm1.2.1 h10
    obtain ⟨-, hb1', hb0'⟩ := hm2'.2.1 h20
    have hreg' : ∀ (l : Fin 3), 0 ≤ (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) →
        ∀ w : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1), w ≠ nodeSrc Γ e₁ →
          0 ≤ w.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
      intro l hb w hw
      by_cases h0 : w = nodeSrc Γ e₀
      · rw [h0]; exact hb
      · exact hoff l w h0 hw
    apply not_linearIndependent_of_simple_pole (nodeSrc Γ e₁)
      ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 0, hint 0⟩)
      ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 1, hint 1⟩)
      ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 2, hint 2⟩) c₀ hc₀0 hc₀ hb1 hb1'
      (hreg' 1 hb0) (hreg' 2 hb0')
    convert hLI using 1
    ext i; fin_cases i <;> rfl
  have hnotboth1 : ¬ ((P 1).rootMultiplicity (ssValue Γ e₁) = 1 ∧ (P 2).rootMultiplicity (ssValue Γ e₁) = 1) := by
    rintro ⟨h11, h21⟩
    have hr1 : (P 1).IsRoot (ssValue Γ e₁) :=
      (Polynomial.rootMultiplicity_pos'.mp (by omega)).2
    have hr2 : (P 2).IsRoot (ssValue Γ e₁) :=
      (Polynomial.rootMultiplicity_pos'.mp (by omega)).2
    obtain ⟨c, hc0, hc⟩ := exists_smul_eq_of_isRoot (P 1) (P 2) (hPli.ne_zero ⟨1, by decide⟩)
      (hPli.ne_zero ⟨2, by decide⟩) (hdegP 1 (by decide)) (hdegP 2 (by decide)) _ hr1 hr2
    have hinj : Function.Injective (![⟨1, by decide⟩, ⟨2, by decide⟩] : Fin 2 → {l : Fin 3 // 1 ≤ (l : ℕ)}) := by
      intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
    have hpair : LinearIndependent (IsLocalRing.ResidueField ↥A) ![P 1, P 2] := by
      convert hPli.comp _ hinj using 1
      ext i; fin_cases i <;> rfl
    rw [LinearIndependent.pair_iff] at hpair
    have := hpair 1 (-c) (by rw [one_smul, neg_smul, hc, add_neg_cancel])
    exact one_ne_zero this.1

  have hcase : ((P 1).rootMultiplicity (ssValue Γ e₁) = 0 ∧ (P 2).rootMultiplicity (ssValue Γ e₁) = 1) ∨
      ((P 1).rootMultiplicity (ssValue Γ e₁) = 1 ∧ (P 2).rootMultiplicity (ssValue Γ e₁) = 0) := by
    have h1 := hm1.2.2; have h2 := hm2'.2.2
    rcases Nat.eq_zero_or_pos ((P 1).rootMultiplicity (ssValue Γ e₁)) with h | h <;>
      rcases Nat.eq_zero_or_pos ((P 2).rootMultiplicity (ssValue Γ e₁)) with h' | h'
    · exact absurd ⟨h, h'⟩ hnotboth0
    · exact Or.inl ⟨h, by omega⟩
    · exact Or.inr ⟨by omega, h'⟩
    · exact absurd ⟨by omega, by omega⟩ hnotboth1

  have assemble : ∀ (l₂ l₃ : Fin 3), l₂ ≠ l₃ → 1 ≤ (l₂ : ℕ) → 1 ≤ (l₃ : ℕ) →
      (P l₂).rootMultiplicity (ssValue Γ e₁) = 0 → (P l₃).rootMultiplicity (ssValue Γ e₁) = 1 →
      ∃ (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (l₂ l₃ : Fin 3),
      l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
      hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 3 ∧
      ∀ e : Fin (mAnnuli 11),
        (ssValue Γ e = 1728 →
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩) = 1 ∧
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint l₂⟩) = -1 ∧
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩) = 2) ∧
        (ssValue Γ e = 0 →
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩) = 1 ∧
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₃, hint l₃⟩) = -1) := by
    intro l₂ l₃ hne23 hl₂ hl₃ h20 h31
    obtain ⟨hn2, hb2, -⟩ := (member l₂ hl₂).2.1 h20
    obtain ⟨hn3, hb3, hm30⟩ := (member l₃ hl₃).1 h31
    refine ⟨hintT, l₂, l₃, hne23, hl₂, hl₃, hn2, hn3, fun e => ⟨fun he => ?_, fun he => ?_⟩⟩
    · have hee : e = e₁ := ssValue_injective Γ (he.trans he₁.symm)
      subst hee
      refine ⟨?_, hb2, ?_⟩
      · rw [hα l₂ hl₂, h20]; norm_num
      · rw [hα l₃ hl₃, h31]; norm_num
    · have hee : e = e₀ := ssValue_injective Γ (he.trans he₀.symm)
      subst hee
      refine ⟨?_, hb3⟩
      rw [hα l₃ hl₃, hm30]; norm_num
  rcases hcase with ⟨h10, h21⟩ | ⟨h11, h20⟩
  · exact assemble 1 2 (by decide) (by decide) (by decide) h10 h21
  · exact assemble 2 1 (by decide) (by decide) (by decide) h20 h11

end S_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven
end P2MW
export P2MW.S_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven (solution)
