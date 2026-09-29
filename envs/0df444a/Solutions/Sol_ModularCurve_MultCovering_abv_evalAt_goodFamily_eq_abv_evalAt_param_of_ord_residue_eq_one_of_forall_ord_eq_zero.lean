-- Prove2me | solution 1 for ModularCurve.MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a54821b8-c4b7-5c74-83cc-42a7105944ab

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar PlaceSpecialization.jFun PlaceSpecialization jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt hasseExp goodFamilyZero FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero"
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
p2m_export "ModularCurve" "embDivisor cuspInftyBar modularFunctionFieldBar PlaceSpecialization.jFun PlaceSpecialization jWidth deg_eq_one_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "AnnCtx mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart src tgt ssValue nodeSrc nodeTgt hasseExp goodFamilyZero FamCtx goodFamily zeroChart_residue_goodFamilyZero_ne_zero infChart_goodFamily_residue_ne_zero"
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

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p)) (l : Fin r)
    (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hzf : ∀ R ∈ (Δ.annIn e).dom, R.ord (goodFamily Φ l) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) ∧
      (∃ h0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, h0⟩) = -1) ∧
      ∀ R ∈ (Δ.annIn e).dom,
        R.IsRational ∧ goodFamily Φ l ∈ R.toValuationSubring ∧
        μ (R.evalAt (goodFamily Φ l)) = μ (R.evalAt (Δ.annOut e).param) ∧
        μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) < μ (R.evalAt (Δ.annOut e).param) := by
  intro μ hμA
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨-, hzoC, hzoord, -⟩ := Δ.attached_tgt e
  obtain ⟨-, hziC, hziord, -⟩ := Δ.attached_src e
  obtain ⟨hintInf, hresInf⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZero, hresZero⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have hscaled := goodFamilyZero_eq_inv_mul' Φ l
  set C := chart Γ (tgt p e) with hC_def
  set C' := chart Γ (src p e) with hC'_def
  set zo := (Δ.annOut e).param with hzo
  set zi := (Δ.annIn e).param with hzi
  set c' : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc'
  set h : modularFunctionFieldBar (1 * p) := goodFamily Φ l with hh
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem hpA _
  have hCinf : h ∈ C.integers := hintInf l
  have hresinf : C.residue ⟨h, hCinf⟩ ≠ 0 := hresInf l
  have hordT : (nodeTgt Γ e).ord (C.residue ⟨h, hCinf⟩) = 1 := hord
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * h ∈ C'.integers := by
    rw [← hscaled]; exact hintZero l
  have hres' : C'.residue ⟨_, hC'⟩ ≠ 0 := by
    have e1 : (⟨_, hC'⟩ : C'.integers) = ⟨_, hintZero l⟩ := Subtype.ext hscaled.symm
    rw [e1]; exact hresZero l
  have hh0 : h ≠ 0 := goodFamily_ne_zero' Φ l

  have hzores0 : C.residue ⟨zo, hzoC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzoord; exact zero_ne_one hzoord
  have hzires0 : C'.residue ⟨zi, hziC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hziord; exact zero_ne_one hziord
  have hzi0 : zi ≠ 0 := by
    intro h0; apply hzires0
    have : (⟨zi, hziC⟩ : C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hzo0 : zo ≠ 0 := by
    intro h0; apply hzores0
    have : (⟨zo, hzoC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord h := by
    intro Q hQ
    rw [hh, (hzf Q (hdom ▸ hQ))]
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have htwo' : zi * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [show zi * zo = zo * zi from mul_comm _ _, hzo, hzi, htwo, hmod]
  have hmod0' : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0

  obtain ⟨D, -, hDsupp, hDord, hdeg, hsum⟩ :=
    AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo'
      C (nodeTgt Γ e) (Δ.attached_tgt e) C' (nodeSrc Γ e) (Δ.attached_src e)
      hwide h hCinf hresinf c' hc'0 hc'A hC' hres' hpole
  have hD0 : D = 0 := by
    ext Q
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hQ : Q ∈ (Δ.annOut e).dom
    · rw [hDord Q hQ, hh]; exact hzf Q (hdom ▸ hQ)
    · by_contra hne; exact hQ (hDsupp Q hne)
  rw [hD0, Finsupp.sum_zero_index] at hdeg hsum
  have ha' : (nodeSrc Γ e).ord (C'.residue ⟨_, hC'⟩) = -1 := by rw [hordT] at hdeg; omega
  have hlogeq : Real.log (μ c') = Real.log (μ ((Δ.annOut e).modulus : AlgebraicClosure ℚ)) := by
    rw [ha'] at hsum; push_cast at hsum; linarith
  have hμeq : μ c' = μ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) :=
    Real.log_injOn_pos (Set.mem_Ioi.2 (μ.pos hc'0)) (Set.mem_Ioi.2 (μ.pos hmod0')) hlogeq

  have hzoinv : zo⁻¹ ∈ C.integers := vs_inv_mem_of_isUnit_D hzoC (chart_isUnit_of_residue_ne_zero_D C hzoC hzores0)
  set h₂ : modularFunctionFieldBar (1 * p) := h * zo⁻¹ with hh₂
  have hh₂0 : h₂ ≠ 0 := mul_ne_zero hh0 (inv_ne_zero hzo0)
  have hh₂C : h₂ ∈ C.integers := mul_mem hCinf hzoinv
  have hh₂res : C.residue ⟨h₂, hh₂C⟩ = C.residue ⟨h, hCinf⟩ * (C.residue ⟨zo, hzoC⟩)⁻¹ := by
    have e1 : (⟨h₂, hh₂C⟩ : C.integers) = ⟨h, hCinf⟩ * ⟨zo⁻¹, hzoinv⟩ := Subtype.ext rfl
    rw [e1, map_mul, chart_residue_inv_D C hzoC hzores0 hzoinv]
  have hh₂res0 : C.residue ⟨h₂, hh₂C⟩ ≠ 0 := by
    rw [hh₂res]; exact mul_ne_zero hresinf (inv_ne_zero hzores0)
  have hh₂ord : (nodeTgt Γ e).ord (C.residue ⟨h₂, hh₂C⟩) = 0 := by
    rw [hh₂res, (nodeTgt Γ e).ord_mul hresinf (inv_ne_zero hzores0), Place.ord_inv, hordT, hzoord]
    ring
  set c₂ : AlgebraicClosure ℚ := c' * (((Δ.annOut e).modulus : AlgebraicClosure ℚ))⁻¹ with hc₂
  have hc₂0 : c₂ ≠ 0 := mul_ne_zero hc'0 (inv_ne_zero hmod0')
  have hμc₂ : μ c₂ = 1 := by rw [hc₂, map_mul, map_inv₀, hμeq, mul_inv_cancel₀ (μ.pos hmod0').ne']
  have hc₂A : c₂ ∈ A := (hμA _).2 hμc₂.le
  have hzo_eq : zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut e).modulus : AlgebraicClosure ℚ) * zi⁻¹ := by
    rw [← htwo', mul_comm zi zo, mul_inv_cancel_right₀ hzi0]
  have hP : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c' ≠ 0 := (map_ne_zero _).2 hc'0
  have hMOD : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).2 hmod0'
  have key : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₂)⁻¹ * h₂
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * h * zi := by
    rw [hh₂, hzo_eq, hc₂, map_mul, map_inv₀]
    field_simp
  have hC'₂ : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₂)⁻¹ * h₂ ∈ C'.integers := by
    rw [key]; exact mul_mem hC' hziC
  have hres'₂eq : C'.residue ⟨_, hC'₂⟩ = C'.residue ⟨_, hC'⟩ * C'.residue ⟨zi, hziC⟩ := by
    have e1 : (⟨_, hC'₂⟩ : C'.integers) = ⟨_, hC'⟩ * ⟨zi, hziC⟩ := Subtype.ext key
    rw [e1, map_mul]
  have hres'₂ : C'.residue ⟨_, hC'₂⟩ ≠ 0 := by rw [hres'₂eq]; exact mul_ne_zero hres' hzires0
  have hord'₂ : (nodeSrc Γ e).ord (C'.residue ⟨_, hC'₂⟩) = 0 := by
    rw [hres'₂eq, (nodeSrc Γ e).ord_mul hres' hzires0, ha', hziord]; ring
  have hpole₂ : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord h₂ := by
    intro Q hQ
    obtain ⟨-, hzoQ, -, hzoQ0, -⟩ := (Δ.annOut e).mem_dom Q hQ
    have hzoQord : Q.ord zo = 0 := ord_eq_zero_of_evalAt_ne_zero_D Q hzoQ hzoQ0
    rw [hh₂, Q.ord_mul hh0 (inv_ne_zero hzo0), Place.ord_inv, hzoQord]
    simpa using hpole Q hQ
  obtain ⟨-, -, hc⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo'
    C (nodeTgt Γ e) (Δ.attached_tgt e) C' (nodeSrc Γ e) (Δ.attached_src e)
    hwide h₂ hh₂C hh₂res0 c₂ hc₂0 hc₂A hC'₂ hres'₂ hpole₂

  refine ⟨by rw [← hmod, ← hμeq, hc', map_pow], ⟨hintZero l, ?_⟩, fun R hR => ?_⟩
  · have e1 : (⟨_, hintZero l⟩ : C'.integers) = ⟨_, hC'⟩ := Subtype.ext hscaled
    show (nodeSrc Γ e).ord (C'.residue ⟨_, hintZero l⟩) = -1
    rw [e1]; exact ha'
  have hRout : R ∈ (Δ.annOut e).dom := hdom ▸ hR
  obtain ⟨hordh₂, hμh₂⟩ := hc ⟨hμc₂, hh₂ord, hord'₂⟩ R hRout
  obtain ⟨hRrat, hzoR, -, hzoR0, m, hm𝔪, hm⟩ := (Δ.annOut e).mem_dom R hRout
  have hh₂R : h₂ ∈ R.toValuationSubring := R.mem_of_ord_nonneg hh₂0 hordh₂.symm.le
  have hh_eq : h = h₂ * zo := by rw [hh₂, inv_mul_cancel_right₀ hzo0]
  have hhR : h ∈ R.toValuationSubring := by rw [hh_eq]; exact mul_mem hh₂R hzoR
  refine ⟨hRrat, hhR, ?_, ?_⟩
  · rw [hh_eq, evalAt_mul_D R hRrat hh₂R hzoR, map_mul, hμh₂, one_mul]
  · rw [← hmod, hm, map_mul]
    have hz0 : 0 < μ (R.evalAt zo) := μ.pos hzoR0
    have hm1 : μ (m : AlgebraicClosure ℚ) < 1 := abv_lt_one_of_mem_maximalIdeal_D μ hμA hm𝔪
    calc μ (R.evalAt zo) * μ (m : AlgebraicClosure ℚ) < μ (R.evalAt zo) * 1 := mul_lt_mul_of_pos_left hm1 hz0
      _ = μ (R.evalAt zo) := mul_one _

end S_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
end P2MW
export P2MW.S_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero (solution)
