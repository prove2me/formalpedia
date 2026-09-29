-- Prove2me | solution 1 for ModularCurve.MultCovering.ord_nodeTgt_infChart_residue_of_digits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/93e3a911-e26a-5427-9f4e-593ee0ae94ec

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_ord_nodeTgt_infChart_residue_of_digits
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering Polynomial

namespace SLC

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ssPolyBar_eq_aeval :
    ssPolyBar Γ = aeval (jBar (ResidueField ↥A)) (∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e))) := by
  unfold ssPolyBar
  rw [map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_sub, aeval_X, aeval_C]

theorem rootMultiplicity_prod_X_sub_C (e : Fin (mAnnuli p)) :
    (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))).rootMultiplicity (ssValue Γ e) = 1 := by
  classical
  have hne : (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e' _ => X_sub_C_ne_zero _
  rw [← Polynomial.count_roots, Polynomial.roots_prod _ _ hne]
  simp only [Polynomial.roots_X_sub_C, Multiset.count_bind, Multiset.count_singleton]
  rw [show (Finset.univ.val.map fun e' : Fin (mAnnuli p) => if ssValue Γ e = ssValue Γ e' then 1 else 0).sum
      = ∑ e' : Fin (mAnnuli p), (if ssValue Γ e = ssValue Γ e' then 1 else 0) from rfl]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne'
    rw [if_neg]
    exact fun h => hne' ((ssValue_injective Γ) h).symm
  · simp

theorem aeval_jBar_ne_zero [IsAlgClosed (ResidueField ↥A)] (Q : Polynomial (ResidueField ↥A)) (hQ : Q ≠ 0)
    (e : Fin (mAnnuli p)) :
    ssPolyBar Γ * aeval (jBar (ResidueField ↥A)) Q ≠ 0 := by
  intro h

  have hord := ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity (ResidueField ↥A) (ssValue Γ e)
    ((∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) * Q)
  have hne : (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) * Q ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun e' _ => X_sub_C_ne_zero _) hQ
  rw [map_mul, ← ssPolyBar_eq_aeval, show (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) 1)) = jBar (ResidueField ↥A) from rfl, h,
    Polynomial.rootMultiplicity_mul hne, rootMultiplicity_prod_X_sub_C] at hord
  have h0 : (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord (0 : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) = 0 :=
    Place.ord_zero _
  rw [h0] at hord
  omega

theorem ord_nodeTgt_ssPolyBar_mul_aeval [IsAlgClosed (ResidueField ↥A)] (Q : Polynomial (ResidueField ↥A)) (hQ : Q ≠ 0)
    (e : Fin (mAnnuli p)) :
    (nodeTgt Γ e).ord (ssPolyBar Γ * aeval (jBar (ResidueField ↥A)) Q) = 1 + Q.rootMultiplicity (ssValue Γ e) := by
  rw [ssPolyBar_eq_aeval, ← map_mul]
  have hne : (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) * Q ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun e' _ => X_sub_C_ne_zero _) hQ
  rw [show nodeTgt Γ e = charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e) from rfl,
    show (jBar (ResidueField ↥A)) = (⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) 1)) from rfl,
    ModularCurve.ord_charLGeomPlaceOfPoint_aeval_jqModC_eq_rootMultiplicity _ _ _, Polynomial.rootMultiplicity_mul hne,
    rootMultiplicity_prod_X_sub_C]
  push_cast
  ring

theorem rootMultiplicity_le_one_of_eval_derivative_ne_zero {k : Type*} [CommRing k] [IsDomain k]
    (Q : Polynomial k) (a : k) (h : (derivative Q).eval a ≠ 0) : Q.rootMultiplicity a ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  exact h (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt)

end SLC

open SLC in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hintI : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (P : Fin r → Polynomial (ResidueField ↥A))
    (hP : ∀ l : Fin r, 1 ≤ (l : ℕ) → (P l).natDegree + 1 ≤ mAnnuli p ∧
      (infChart Γ).residue ⟨Φ.t l, hintI l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l))
    (hPLI : LinearIndependent (ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l))
    (d : Fin r → Fin r → ZMod p)
    (t' : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hintI' : ∀ l, t' l ∈ (infChart Γ).integers)
    (h0 : ∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨t' l, hintI' l⟩ = 1)
    (hres : ∀ i : Fin r, 1 ≤ (i : ℕ) → (infChart Γ).residue ⟨t' i, hintI' i⟩
      = ∑ j : Fin r, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
          (if hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j then ((d i j).val : ResidueField ↥A) else 0)
          * (infChart Γ).residue ⟨Φ.t j, hintI j⟩)

    (hav0 : ∀ (e : Fin (mAnnuli p)) (j : Fin r), 1 ≤ (j : ℕ) → hasseExp Φ.toFamData j = 2 →
      jWidth (ssValue Γ e) = 1 → (P j).eval (ssValue Γ e) = 0)
    (hav1 : ∀ (e : Fin (mAnnuli p)) (i : Fin r), 1 ≤ (i : ℕ) →
      (jWidth (ssValue Γ e) ≠ 1 ∨ hasseExp Φ.toFamData i = 1) →
      (∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j
          then ((d i j).val : ResidueField ↥A) else 0) • P j).eval (ssValue Γ e) ≠ 0)
    (hav2 : ∀ (e : Fin (mAnnuli p)) (i : Fin r), 1 ≤ (i : ℕ) → hasseExp Φ.toFamData i = 2 → jWidth (ssValue Γ e) = 1 →
      (Polynomial.derivative (∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j
          then ((d i j).val : ResidueField ↥A) else 0) • P j)).eval (ssValue Γ e) ≠ 0) :
    (∀ l, (infChart Γ).residue ⟨t' l, hintI' l⟩ ≠ 0) ∧
    (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → jWidth (ssValue Γ e) ≠ 1 →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' l, hintI' l⟩) = 1) ∧
    (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 1 →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' l, hintI' l⟩) = 1) ∧
    (∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 2 → jWidth (ssValue Γ e) = 1 →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' l, hintI' l⟩) = 2) := by
  classical
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hp : p.Prime := Fact.out

  have hm : 0 < mAnnuli p := by unfold mAnnuli; omega
  let e₀ : Fin (mAnnuli p) := ⟨0, hm⟩

  have h1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := one_le_hasseExp p A hA Γ Φ
  have h2 : ∀ l : Fin r, hasseExp Φ.toFamData l ≤ 2 := hasseExp_le_two_of_thirteen_le p hp13 A hA Γ Δ Φ
  have h0' : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp Φ.toFamData l = 0 := hasseExp_zero Φ

  let N : Fin r → Polynomial (ResidueField ↥A) := fun i =>
    ∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j
      then ((d i j).val : ResidueField ↥A) else 0) • P j

  have hnum : ∀ i : Fin r, 1 ≤ (i : ℕ) →
      (infChart Γ).residue ⟨t' i, hintI' i⟩ = ssPolyBar Γ * aeval (jBar (ResidueField ↥A)) (N i) := by
    intro i hi
    rw [hres i hi, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : 1 ≤ (j : ℕ)
    · rw [(hP j hj).2, map_smul, Algebra.smul_def]
      simp only [hj, true_and]
      ring
    · have hj0 : (j : ℕ) = 0 := by omega
      have hlt : ¬ hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j := by
        rw [h0' j hj0]; have := h1 i hi; omega
      simp only [hj, false_and, if_false, hlt, zero_smul, map_zero, zero_mul, mul_zero]

  have hN0 : ∀ i : Fin r, 1 ≤ (i : ℕ) → N i ≠ 0 := by
    intro i hi hzero
    have hc : hasseExp Φ.toFamData i = 1 ∨ hasseExp Φ.toFamData i = 2 := by
      have := h1 i hi; have := h2 i; omega
    by_cases hw : jWidth (ssValue Γ e₀) ≠ 1
    · exact hav1 e₀ i hi (Or.inl hw) (by rw [show (∑ j : Fin r, _) = N i from rfl, hzero, eval_zero])
    · push_neg at hw
      rcases hc with hc | hc
      · exact hav1 e₀ i hi (Or.inr hc) (by rw [show (∑ j : Fin r, _) = N i from rfl, hzero, eval_zero])
      · exact hav2 e₀ i hi hc hw (by rw [show (∑ j : Fin r, _) = N i from rfl, hzero, derivative_zero, eval_zero])

  have hord : ∀ (e : Fin (mAnnuli p)) (i : Fin r), 1 ≤ (i : ℕ) →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨t' i, hintI' i⟩) = 1 + (N i).rootMultiplicity (ssValue Γ e) := by
    intro e i hi
    rw [hnum i hi]
    exact ord_nodeTgt_ssPolyBar_mul_aeval Γ (N i) (hN0 i hi) e
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro l
    by_cases hl : 1 ≤ (l : ℕ)
    · rw [hnum l hl]; exact aeval_jBar_ne_zero Γ (N l) (hN0 l hl) e₀
    · rw [h0 l (by omega)]; exact one_ne_zero
  ·
    intro e l hl hw
    rw [hord e l hl, (Polynomial.rootMultiplicity_eq_zero_iff).mpr, Nat.cast_zero, add_zero]
    intro hroot
    exact absurd hroot (hav1 e l hl (Or.inl hw))
  ·
    intro e l hl hc
    rw [hord e l hl, (Polynomial.rootMultiplicity_eq_zero_iff).mpr, Nat.cast_zero, add_zero]
    intro hroot
    exact absurd hroot (hav1 e l hl (Or.inr hc))
  ·
    intro e l hl hc hw
    rw [hord e l hl]
    have hle : (N l).rootMultiplicity (ssValue Γ e) ≤ 1 :=
      rootMultiplicity_le_one_of_eval_derivative_ne_zero (N l) (ssValue Γ e) (hav2 e l hl hc hw)
    have hge : 1 ≤ (N l).rootMultiplicity (ssValue Γ e) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Polynomial.rootMultiplicity_eq_zero_iff, Classical.not_imp]
      refine ⟨?_, hN0 l hl⟩

      show (N l).IsRoot (ssValue Γ e)
      rw [IsRoot, show N l = ∑ j : Fin r, _ from rfl, eval_finset_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [eval_smul, smul_eq_mul]
      by_cases hj : 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData l ≤ hasseExp Φ.toFamData j
      · have hj2 : hasseExp Φ.toFamData j = 2 := by have := h2 j; omega
        rw [hav0 e j hj.1 hj2 hw, mul_zero]
      · rw [if_neg hj, zero_mul]
    omega

end S_ModularCurve_MultCovering_ord_nodeTgt_infChart_residue_of_digits
end P2MW
export P2MW.S_ModularCurve_MultCovering_ord_nodeTgt_infChart_residue_of_digits (solution)
