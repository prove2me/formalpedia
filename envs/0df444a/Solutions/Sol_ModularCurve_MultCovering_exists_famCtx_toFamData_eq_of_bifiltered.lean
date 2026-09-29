-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_famCtx_toFamData_eq_of_bifiltered
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3cb1f49d-8f31-5dd6-bbb6-aa9d386db489

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.MultCovering.AnnCtx.mk.sizeOf_spec ModularCurve.MultCovering.AnnCtx.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem residue_algebraMap_rat_eq_zero_of_padicValRat_pos (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (q : ℚ) (hq : q ≠ 0)
    (hv : 1 ≤ padicValRat p q) (hmem : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A) :
    IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hmem⟩ = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  set q' : ℚ := q / p with hq'
  have hq'0 : q' ≠ 0 := div_ne_zero hq hp0
  have hqq' : q = p * q' := by rw [hq', mul_div_cancel₀ q hp0]
  have hvq' : 0 ≤ padicValRat p q' := by
    have h1 : padicValRat p q = padicValRat p (p : ℚ) + padicValRat p q' := by
      rw [hqq', padicValRat.mul hp0 hq'0]
    rw [padicValRat.self hp.one_lt] at h1
    linarith
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  have hq'A : ((q' : ℚ) : AlgebraicClosure ℚ) ∈ A :=
    (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq'0).2 hvq'
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(p : AlgebraicClosure ℚ), hpA⟩)).1 hA
  have e1 : (⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hmem⟩ : ↥A)
      = ⟨(p : AlgebraicClosure ℚ), hpA⟩ * ⟨((q' : ℚ) : AlgebraicClosure ℚ), hq'A⟩ := by
    apply Subtype.ext
    show algebraMap ℚ (AlgebraicClosure ℚ) q = (p : AlgebraicClosure ℚ) * ((q' : ℚ) : AlgebraicClosure ℚ)
    rw [eq_ratCast, hqq']; push_cast; ring
  rw [e1]
  exact (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_right _ _ hp𝔪)

namespace Fin p2m_export "Fin" "cast_zero" end Fin
p2m_open_scoped "Fin" in

theorem Fin.sum_eq_sum_subtype_one_le {M : Type*} [AddCommMonoid M] {r : ℕ} (f : Fin r → M)
    (h0 : ∀ j : Fin r, ¬ 1 ≤ (j : ℕ) → f j = 0) :
    ∑ j, f j = ∑ j : {l : Fin r // 1 ≤ (l : ℕ)}, f j := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin r => 1 ≤ (l : ℕ)) (by intro x; simp)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  apply h0
  simpa using hj

namespace Polynomial p2m_export "Polynomial" "C map_injective X coeff aeval degreeLT mem_degreeLE degree mem_degreeLT natDegree_le_of_degree_le map degreeLE sum natDegree degree_le_natDegree pow natDegree_lt_iff_degree_lt mod ext ring" end Polynomial
p2m_open_scoped "Polynomial" in

theorem Polynomial.natDegree_add_one_le_of_mem_degreeLT {k : Type*} [Semiring k] {m : ℕ} {f : Polynomial k}
    (hf : f ∈ Polynomial.degreeLT k m) (hm : 1 ≤ m) : f.natDegree + 1 ≤ m := by
  rw [Polynomial.mem_degreeLT] at hf
  by_cases h0 : f = 0
  · subst h0; simp; exact hm
  · have : f.natDegree < m := (Polynomial.natDegree_lt_iff_degree_lt h0).2 hf
    omega

theorem solution (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (U : Matrix (Fin r) (Fin r) ℚ) (hUunit : IsUnit U)
    (hU : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j) ∨ U i j = 0)
    (hUinv : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0)
    (hU0 : ∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0)
    (D' : FamData p r)
    (htRat : ∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j)
    (ht : ∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
        (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j)
    (hexp : ∀ l, hasseExp D' l = hasseExp Φ.toFamData l) :
    ∃ Φ' : FamCtx p r, Φ'.toFamData = D' := by
  have ht_zero : ∀ l : Fin r, (l : ℕ) = 0 → D'.t l = 1 := by
    intro l hl
    rw [ht l]
    have : ∀ j : Fin r, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j
        = if (j : ℕ) = 0 then Φ.t j else 0 := by
      intro j; rw [hU0 l j hl]; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    have h0 : ∀ j : Fin r, ((j : ℕ) = 0) ↔ j = l := fun j => by constructor <;> intro h <;> [exact Fin.ext (by omega); (subst h; exact hl)]
    simp_rw [h0, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Φ.t_zero l hl

  set Ubar : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U with hUbar
  have hUbar_unit : IsUnit Ubar := hUunit.map _
  have hUbar_det : IsUnit Ubar.det := (Matrix.isUnit_iff_isUnit_det _).1 hUbar_unit
  have htcomb : ∀ i, D'.t i = ∑ j, Ubar i j • Φ.t j := by
    intro i; rw [ht i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]; rfl
  have htcomb' : ∀ j, Φ.t j = ∑ i, Ubar⁻¹ j i • D'.t i := by
    intro j
    simp_rw [htcomb, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ k, (∑ i, Ubar⁻¹ j i * Ubar i k) • Φ.t k = (if j = k then (1 : AlgebraicClosure ℚ) else 0) • Φ.t k := by
      intro k
      have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul Ubar hUbar_det) j) k
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1
      rw [h1]
    simp_rw [← Finset.sum_smul, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have ht_basis : IsEmbBasis (1 * p) D'.t := by
    constructor
    · rw [Fintype.linearIndependent_iff]
      intro g hg

      have hsum : ∑ j, (∑ i, g i * Ubar i j) • Φ.t j = 0 := by
        rw [← hg]
        simp_rw [htcomb, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hcoef : ∀ j, ∑ i, g i * Ubar i j = 0 := (Fintype.linearIndependent_iff.1 Φ.t_basis.1) _ hsum
      have hvec : Matrix.vecMul g Ubar = 0 := by
        ext j; simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]; exact hcoef j
      have := Matrix.eq_zero_of_vecMul_eq_zero hUbar_det.ne_zero hvec
      exact fun i => congrFun this i
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [htcomb i, ← Φ.t_basis.2]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [← Φ.t_basis.2, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        rw [htcomb' j]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hp : p.Prime := Fact.out
  have pint_mem : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (q : ℚ),
      (q = 0 ∨ 0 ≤ padicValRat p q) → algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
    intro A hA q hq
    rw [eq_ratCast]
    rcases eq_or_ne q 0 with rfl | hq0
    · simp
    rcases hq with h | h
    · exact absurd h hq0
    have hAp : A.valuation (p : (AlgebraicClosure ℚ)) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
    exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq0).2 h
  have hfilt : ∀ i j, U i j = 0 ∨ 0 ≤ padicValRat p (U i j) := by
    intro i j; rcases hU i j with h | h
    · exact Or.inr ((le_max_left _ _).trans h)
    · exact Or.inl h
  have hfilt' : ∀ i j, U⁻¹ i j = 0 ∨ 0 ≤ padicValRat p (U⁻¹ i j) := by
    intro i j; rcases hUinv i j with h | h
    · exact Or.inr ((le_max_left _ _).trans h)
    · exact Or.inl h
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hUunit)
  have hUU' : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U ((Matrix.isUnit_iff_isUnit_det U).1 hUunit)
  have ht_inf : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      ∃ hint : ∀ l, D'.t l ∈ (infChart Γ).integers,
        (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨D'.t l, hint l⟩ = 1) ∧
        ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
          (∀ l : Fin r, 1 ≤ (l : ℕ) →
            (P l).natDegree + 1 ≤ mAnnuli p ∧
            (infChart Γ).residue ⟨D'.t l, hint l⟩
              = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
          LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
          Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
            = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
    intro A hA _ _ Γ
    set C := infChart Γ with hC

    set a : Fin r → Fin r → ↥A := fun i j => ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U i j), pint_mem A hA _ (hfilt i j)⟩ with ha
    set a' : Fin r → Fin r → ↥A := fun i j => ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U⁻¹ i j), pint_mem A hA _ (hfilt' i j)⟩ with ha'
    set M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField ↥A) := fun i j => IsLocalRing.residue ↥A (a i j) with hM
    set M' : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField ↥A) := fun i j => IsLocalRing.residue ↥A (a' i j) with hM'

    have haa : (fun i j => (a i j : (AlgebraicClosure ℚ))) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U := by
      ext i j; rfl
    have hAmat : (Matrix.of fun i j => a i j) * (Matrix.of fun i j => a' i j) = (1 : Matrix (Fin r) (Fin r) ↥A) := by
      apply Matrix.map_injective (f := algebraMap ↥A (AlgebraicClosure ℚ)) (fun x y h => Subtype.ext h)
      show ((Matrix.of fun i j => a i j) * (Matrix.of fun i j => a' i j)).map (algebraMap ↥A (AlgebraicClosure ℚ))
        = (1 : Matrix (Fin r) (Fin r) ↥A).map (algebraMap ↥A (AlgebraicClosure ℚ))
      rw [Matrix.map_mul]
      have e1 : (Matrix.of fun i j => a i j).map (algebraMap ↥A (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U := by
        ext i j; rfl
      have e2 : (Matrix.of fun i j => a' i j).map (algebraMap ↥A (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U⁻¹ := by
        ext i j; rfl
      have e3 : (1 : Matrix (Fin r) (Fin r) ↥A).map (algebraMap ↥A (AlgebraicClosure ℚ)) = 1 :=
        Matrix.map_one _ (map_zero _) (map_one _)
      rw [e1, e2, e3, ← map_mul, hUU, map_one]
    have hAmat' : (Matrix.of fun i j => a' i j) * (Matrix.of fun i j => a i j) = (1 : Matrix (Fin r) (Fin r) ↥A) := by
      apply Matrix.map_injective (f := algebraMap ↥A (AlgebraicClosure ℚ)) (fun x y h => Subtype.ext h)
      show ((Matrix.of fun i j => a' i j) * (Matrix.of fun i j => a i j)).map (algebraMap ↥A (AlgebraicClosure ℚ))
        = (1 : Matrix (Fin r) (Fin r) ↥A).map (algebraMap ↥A (AlgebraicClosure ℚ))
      rw [Matrix.map_mul]
      have e1 : (Matrix.of fun i j => a i j).map (algebraMap ↥A (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U := by
        ext i j; rfl
      have e2 : (Matrix.of fun i j => a' i j).map (algebraMap ↥A (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix U⁻¹ := by
        ext i j; rfl
      have e3 : (1 : Matrix (Fin r) (Fin r) ↥A).map (algebraMap ↥A (AlgebraicClosure ℚ)) = 1 :=
        Matrix.map_one _ (map_zero _) (map_one _)
      rw [e1, e2, e3, ← map_mul, hUU', map_one]
    have hMM : M * M' = 1 := by
      have := congrArg (fun N : Matrix (Fin r) (Fin r) ↥A => N.map (IsLocalRing.residue ↥A)) hAmat
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one (IsLocalRing.residue ↥A) (map_zero _) (map_one _)] at this
      exact this
    have hM'M : M' * M = 1 := by
      have := congrArg (fun N : Matrix (Fin r) (Fin r) ↥A => N.map (IsLocalRing.residue ↥A)) hAmat'
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one (IsLocalRing.residue ↥A) (map_zero _) (map_one _)] at this
      exact this
    obtain ⟨hint, h0res, P, hP, hPind, hPspan⟩ := Φ.t_inf A hA Γ
    let S := {l : Fin r // 1 ≤ (l : ℕ)}

    have hintD : ∀ l, D'.t l ∈ C.integers := by
      intro l; rw [ht l]
      exact sum_mem fun j _ => mul_mem ((C.algebraMap_mem_iff _).2 (a l j).2) (hint j)
    have hresD : ∀ l, C.residue ⟨D'.t l, hintD l⟩
        = ∑ j, algebraMap (IsLocalRing.ResidueField ↥A) _ (M l j) * C.residue ⟨Φ.t j, hint j⟩ := by
      intro l
      have e1 : (⟨D'.t l, hintD l⟩ : C.integers)
          = ∑ j, ⟨algebraMap (AlgebraicClosure ℚ) _ (a l j : (AlgebraicClosure ℚ)), (C.algebraMap_mem_iff _).2 (a l j).2⟩ * ⟨Φ.t j, hint j⟩ := by
        apply Subtype.ext; push_cast; exact ht l
      rw [e1, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, C.residue_algebraMap]

    have hn0 : ∀ j : Fin r, (j : ℕ) = 0 → hasseExp Φ.toFamData j = 0 := hasseExp_zero Φ
    have hn1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := one_le_hasseExp p A hA Γ Φ

    have hcol : ∀ (V : Matrix (Fin r) (Fin r) ℚ)
        (hV : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (V i j) ∨ V i j = 0)
        (l j : Fin r) (hl : 1 ≤ (l : ℕ)) (hj : (j : ℕ) = 0) (hmem : algebraMap ℚ (AlgebraicClosure ℚ) (V l j) ∈ A),
        IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (V l j), hmem⟩ = 0 := by
      intro V hV l j hl hj hmem
      rcases hV l j with h | h
      · rw [hn0 j hj, Nat.cast_zero, sub_zero] at h
        have h1 : (1 : ℤ) ≤ padicValRat p (V l j) := by
          have := hn1 l hl
          have : (1 : ℤ) ≤ max 0 (hasseExp Φ.toFamData l : ℤ) := le_max_of_le_right (by exact_mod_cast this)
          exact this.trans h
        by_cases h0 : V l j = 0
        · have : (⟨algebraMap ℚ (AlgebraicClosure ℚ) (V l j), hmem⟩ : ↥A) = 0 :=
            Subtype.ext (by show algebraMap ℚ (AlgebraicClosure ℚ) (V l j) = ((0 : ↥A) : (AlgebraicClosure ℚ)); rw [h0, map_zero]; rfl)
          rw [this, map_zero]
        · exact residue_algebraMap_rat_eq_zero_of_padicValRat_pos p A hA _ h0 h1 hmem
      · have : (⟨algebraMap ℚ (AlgebraicClosure ℚ) (V l j), hmem⟩ : ↥A) = 0 :=
          Subtype.ext (by show algebraMap ℚ (AlgebraicClosure ℚ) (V l j) = ((0 : ↥A) : (AlgebraicClosure ℚ)); rw [h, map_zero]; rfl)
        rw [this, map_zero]
    have hM0 : ∀ l j : Fin r, 1 ≤ (l : ℕ) → (j : ℕ) = 0 → M l j = 0 := fun l j hl hj => hcol U hU l j hl hj _
    have hM'0 : ∀ l j : Fin r, 1 ≤ (l : ℕ) → (j : ℕ) = 0 → M' l j = 0 := fun l j hl hj => hcol U⁻¹ hUinv l j hl hj _

    set MS : Matrix S S (IsLocalRing.ResidueField ↥A) := fun i j => M i j with hMS
    set MS' : Matrix S S (IsLocalRing.ResidueField ↥A) := fun i j => M' i j with hMS'
    have hblock : ∀ (X Y : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField ↥A)), X * Y = 1 →
        (∀ l j : Fin r, 1 ≤ (l : ℕ) → (j : ℕ) = 0 → X l j = 0) →
        (Matrix.of fun i j : S => X i j) * (Matrix.of fun i j : S => Y i j) = 1 := by
      intro X Y hXY hX0
      ext i j
      have h1 := congrFun (congrFun hXY i) j
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1 ⊢
      rw [Fin.sum_eq_sum_subtype_one_le (fun l => X i l * Y l j) (fun l hl => by
        show X i l * Y l j = 0
        rw [hX0 i l i.2 (by omega), zero_mul])] at h1
      simp only [Matrix.of_apply]
      rw [h1]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Subtype.ext h))]
    have hMS1 : MS * MS' = 1 := hblock M M' hMM hM0
    have hMS2 : MS' * MS = 1 := hblock M' M hM'M hM'0
    have hMSdet : IsUnit MS.det := Matrix.isUnit_det_of_right_inverse hMS1

    have hm1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ mAnnuli p := fun l hl => by have := (hP l hl).1; omega
    have hPmem : ∀ j : S, P j ∈ Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
      intro j; rw [← hPspan]; exact Submodule.subset_span ⟨j, rfl⟩
    set P' : Fin r → Polynomial (IsLocalRing.ResidueField ↥A) := fun l => ∑ j : S, M l j • P j with hP'
    have hP'mem : ∀ l, P' l ∈ Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := fun l =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hPmem j)
    refine ⟨hintD, fun l hl => ?_, P', fun l hl => ⟨?_, ?_⟩, ?_, ?_⟩
    ·
      have : (⟨D'.t l, hintD l⟩ : C.integers) = 1 := Subtype.ext (ht_zero l hl)
      rw [this, map_one]
    · exact Polynomial.natDegree_add_one_le_of_mem_degreeLT (hP'mem l) (hm1 l hl)
    ·
      rw [hresD l, Fin.sum_eq_sum_subtype_one_le _ (fun j hj => by
        show algebraMap (IsLocalRing.ResidueField ↥A) _ (M l j) * C.residue ⟨Φ.t j, hint j⟩ = 0
        rw [hM0 l j hl (by omega), map_zero, zero_mul])]
      rw [hP', map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hP j j.2).2, map_smul, Algebra.smul_def]; ring
    ·
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hsum : ∑ j : S, (∑ i : S, g i * MS i j) • P j = 0 := by
        rw [← hg]
        simp_rw [hP', Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hcoef : ∀ j : S, ∑ i : S, g i * MS i j = 0 := (Fintype.linearIndependent_iff.1 hPind) _ hsum
      have hvec : Matrix.vecMul g MS = 0 := by
        ext j; simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]; exact hcoef j
      have := Matrix.eq_zero_of_vecMul_eq_zero hMSdet.ne_zero hvec
      exact fun i => congrFun this i
    ·
      apply le_antisymm
      · rw [Submodule.span_le]; rintro _ ⟨l, rfl⟩; exact hP'mem l
      · rw [← hPspan, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show P j ∈ _

        have : P j = ∑ i : S, MS' j i • P' i := by
          simp_rw [hP', Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          have : ∀ k : S, (∑ i : S, MS' j i * M i k) • P k = (if j = k then (1 : IsLocalRing.ResidueField ↥A) else 0) • P k := by
            intro k
            have h1 := congrFun (congrFun hMS2 j) k
            simp only [Matrix.mul_apply, Matrix.one_apply] at h1
            rw [← h1]
          simp_rw [← Finset.sum_smul, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have ht_zeroChart : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      (∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) →
      ∃ (hint : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
        (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
        (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
        (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
          Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
        (∀ l : Fin r, (l : ℕ) = 0 →
          P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
        ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint l⟩ * ssPolyBarZero Γ
          = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := by
    intro A hA _ _ Γ hw1
    obtain ⟨hint0, P0, hdeg0, hLI0, hspan0, hP00, hres0⟩ := Φ.t_zeroChart A hA Γ hw1
    set C := zeroChart Γ with hC
    have hp0Q : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero

    set n : Fin r → ℤ := fun l => (hasseExp Φ.toFamData l : ℤ) with hn
    set W : Matrix (Fin r) (Fin r) ℚ := fun l j => U l j * (p : ℚ) ^ (n j - n l) with hW
    set W' : Matrix (Fin r) (Fin r) ℚ := fun l j => U⁻¹ l j * (p : ℚ) ^ (n j - n l) with hW'
    have hpz : ∀ m : ℤ, ((p : ℚ) ^ m) ≠ 0 := fun m => zpow_ne_zero _ hp0Q
    have hvzpow : ∀ m : ℤ, padicValRat p ((p : ℚ) ^ m) = m := by
      intro m
      rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
      · rw [zpow_natCast, padicValRat.pow _, padicValRat.self hp.one_lt, mul_one]
      · rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow _, padicValRat.self hp.one_lt, mul_one]
    have hWint : ∀ (V : Matrix (Fin r) (Fin r) ℚ)
        (hV : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (V i j) ∨ V i j = 0)
        (l j : Fin r), (V l j * (p : ℚ) ^ (n j - n l) = 0 ∨ 0 ≤ padicValRat p (V l j * (p : ℚ) ^ (n j - n l))) := by
      intro V hV l j
      rcases hV l j with h | h
      · by_cases h0 : V l j = 0
        · left; rw [h0, zero_mul]
        · right
          rw [padicValRat.mul h0 (hpz _), hvzpow]
          have := (le_max_right _ _).trans h
          simp only [hn]; linarith
      · left; rw [h, zero_mul]
    have hWW : W * W' = 1 := by
      ext l j
      have h1 := congrFun (congrFun hUU l) j
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1 ⊢
      simp only [hW, hW']
      have : ∀ k, U l k * (p : ℚ) ^ (n k - n l) * (U⁻¹ k j * (p : ℚ) ^ (n j - n k))
          = (U l k * U⁻¹ k j) * (p : ℚ) ^ (n j - n l) := by
        intro k; rw [show n j - n l = (n k - n l) + (n j - n k) by ring, zpow_add₀ hp0Q]; ring
      simp_rw [this, ← Finset.sum_mul, h1]
      split_ifs with hlj
      · subst hlj; simp
      · rw [zero_mul]
    have hW'W : W' * W = 1 := by
      ext l j
      have h1 := congrFun (congrFun hUU' l) j
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1 ⊢
      simp only [hW, hW']
      have : ∀ k, U⁻¹ l k * (p : ℚ) ^ (n k - n l) * (U k j * (p : ℚ) ^ (n j - n k))
          = (U⁻¹ l k * U k j) * (p : ℚ) ^ (n j - n l) := by
        intro k; rw [show n j - n l = (n k - n l) + (n j - n k) by ring, zpow_add₀ hp0Q]; ring
      simp_rw [this, ← Finset.sum_mul, h1]
      split_ifs with hlj
      · subst hlj; simp
      · rw [zero_mul]

    set b : Fin r → Fin r → ↥A := fun i j => ⟨algebraMap ℚ (AlgebraicClosure ℚ) (W i j), pint_mem A hA _ (hWint U hU i j)⟩ with hb
    set b' : Fin r → Fin r → ↥A := fun i j => ⟨algebraMap ℚ (AlgebraicClosure ℚ) (W' i j), pint_mem A hA _ (hWint U⁻¹ hUinv i j)⟩ with hb'
    set N : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField ↥A) := fun i j => IsLocalRing.residue ↥A (b i j) with hN
    set N' : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField ↥A) := fun i j => IsLocalRing.residue ↥A (b' i j) with hN'
    have hBmat : ∀ (X Y : Matrix (Fin r) (Fin r) ℚ) (hXY : X * Y = 1) (x y : Fin r → Fin r → ↥A)
        (hx : ∀ i j, (x i j : (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) (X i j)) (hy : ∀ i j, (y i j : (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) (Y i j)),
        (Matrix.of fun i j => x i j) * (Matrix.of fun i j => y i j) = (1 : Matrix (Fin r) (Fin r) ↥A) := by
      intro X Y hXY x y hx hy
      apply Matrix.map_injective (f := algebraMap ↥A (AlgebraicClosure ℚ)) (fun u v h => Subtype.ext h)
      show ((Matrix.of fun i j => x i j) * (Matrix.of fun i j => y i j)).map (algebraMap ↥A (AlgebraicClosure ℚ))
        = (1 : Matrix (Fin r) (Fin r) ↥A).map (algebraMap ↥A (AlgebraicClosure ℚ))
      rw [Matrix.map_mul]
      have e1 : (Matrix.of fun i j => x i j).map (algebraMap ↥A (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix X := by
        ext i j; exact hx i j
      have e2 : (Matrix.of fun i j => y i j).map (algebraMap ↥A (AlgebraicClosure ℚ)) = (algebraMap ℚ (AlgebraicClosure ℚ)).mapMatrix Y := by
        ext i j; exact hy i j
      rw [e1, e2, Matrix.map_one _ (map_zero _) (map_one _), ← map_mul, hXY, map_one]
    have hNN : N * N' = 1 := by
      have h := hBmat W W' hWW b b' (fun i j => rfl) (fun i j => rfl)
      have := congrArg (fun X : Matrix (Fin r) (Fin r) ↥A => X.map (IsLocalRing.residue ↥A)) h
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one (IsLocalRing.residue ↥A) (map_zero _) (map_one _)] at this
      exact this
    have hN'N : N' * N = 1 := by
      have h := hBmat W' W hW'W b' b (fun i j => rfl) (fun i j => rfl)
      have := congrArg (fun X : Matrix (Fin r) (Fin r) ↥A => X.map (IsLocalRing.residue ↥A)) h
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one (IsLocalRing.residue ↥A) (map_zero _) (map_one _)] at this
      exact this
    have hNdet : IsUnit N.det := Matrix.isUnit_det_of_right_inverse hNN

    have hgfz : ∀ l, goodFamilyZero D' l = ∑ j, algebraMap (AlgebraicClosure ℚ) _ (b l j : (AlgebraicClosure ℚ)) * goodFamilyZero Φ.toFamData j := by
      intro l
      have e1 : goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) _ ((p : (AlgebraicClosure ℚ)) ^ hasseExp D' l))⁻¹ * D'.t l := rfl
      have e2 : ∀ j, goodFamilyZero Φ.toFamData j = (algebraMap (AlgebraicClosure ℚ) _ ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData j))⁻¹ * Φ.t j :=
        fun j => rfl
      rw [e1, hexp l, ht l, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [e2 j, ← mul_assoc, ← map_inv₀, ← map_mul,
        show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b l j : (AlgebraicClosure ℚ))
            * ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData j))⁻¹ * Φ.t j)
          = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((b l j : (AlgebraicClosure ℚ)) * ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData j)⁻¹) * Φ.t j by
          rw [map_mul, map_inv₀, mul_assoc]]
      congr 2
      show ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l)⁻¹ * algebraMap ℚ (AlgebraicClosure ℚ) (U l j)
        = algebraMap ℚ (AlgebraicClosure ℚ) (U l j * (p : ℚ) ^ (n j - n l)) * ((p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData j)⁻¹
      rw [map_mul, map_zpow₀, map_natCast]
      simp only [hn]
      rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
      field_simp
    have hintD0 : ∀ l, goodFamilyZero D' l ∈ C.integers := by
      intro l; rw [hgfz l]
      exact sum_mem fun j _ => mul_mem ((C.algebraMap_mem_iff _).2 (b l j).2) (hint0 j)
    have hresD0 : ∀ l, C.residue ⟨goodFamilyZero D' l, hintD0 l⟩
        = ∑ j, algebraMap (IsLocalRing.ResidueField ↥A) _ (N l j) * C.residue ⟨goodFamilyZero Φ.toFamData j, hint0 j⟩ := by
      intro l
      have e1 : (⟨goodFamilyZero D' l, hintD0 l⟩ : C.integers)
          = ∑ j, ⟨algebraMap (AlgebraicClosure ℚ) _ (b l j : (AlgebraicClosure ℚ)), (C.algebraMap_mem_iff _).2 (b l j).2⟩ * ⟨goodFamilyZero Φ.toFamData j, hint0 j⟩ := by
        apply Subtype.ext; push_cast; exact hgfz l
      rw [e1, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, C.residue_algebraMap]

    have hn0 : ∀ j : Fin r, (j : ℕ) = 0 → hasseExp Φ.toFamData j = 0 := hasseExp_zero Φ
    have hN0 : ∀ l j : Fin r, (l : ℕ) = 0 → N l j = if (j : ℕ) = 0 then 1 else 0 := by
      intro l j hl
      have hv : ((b l j : ↥A) : (AlgebraicClosure ℚ)) = if (j : ℕ) = 0 then 1 else 0 := by
        show algebraMap ℚ (AlgebraicClosure ℚ) (U l j * (p : ℚ) ^ (n j - n l)) = _
        rw [hU0 l j hl]
        split_ifs with hj
        · simp only [hn]; rw [hn0 j hj, hn0 l hl, sub_self, zpow_zero, mul_one, map_one]
        · rw [zero_mul, map_zero]
      show IsLocalRing.residue ↥A (b l j) = _
      split_ifs with hj
      · rw [if_pos hj] at hv
        have : b l j = 1 := Subtype.ext (by rw [hv]; rfl)
        rw [this, map_one]
      · rw [if_neg hj] at hv
        have : b l j = 0 := Subtype.ext (by rw [hv]; rfl)
        rw [this, map_zero]

    set P' : Fin r → Polynomial (IsLocalRing.ResidueField ↥A) := fun l => ∑ j, N l j • P0 j with hP'
    have hP'mem : ∀ l, P' l ∈ Polynomial.degreeLE (IsLocalRing.ResidueField ↥A) (mAnnuli p) := fun l =>
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Polynomial.mem_degreeLE.2
        ((Polynomial.degree_le_natDegree).trans (by exact_mod_cast hdeg0 j)))
    refine ⟨hintD0, P', fun l => ?_, ?_, ?_, fun l hl => ?_, fun l => ?_⟩
    · exact Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.1 (hP'mem l))
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      have hsum : ∑ j, (∑ i, g i * N i j) • P0 j = 0 := by
        rw [← hg]
        simp_rw [hP', Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
      have hcoef : ∀ j, ∑ i, g i * N i j = 0 := (Fintype.linearIndependent_iff.1 hLI0) _ hsum
      have hvec : Matrix.vecMul g N = 0 := by
        ext j; simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]; exact hcoef j
      have := Matrix.eq_zero_of_vecMul_eq_zero hNdet.ne_zero hvec
      exact fun i => congrFun this i
    · intro Q hQ
      have hQ' := hspan0 Q hQ
      refine Submodule.span_le.2 ?_ hQ'
      rintro _ ⟨j, rfl⟩
      show P0 j ∈ _
      have : P0 j = ∑ i, N' j i • P' i := by
        simp_rw [hP', Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ k, (∑ i, N' j i * N i k) • P0 k = (if j = k then (1 : IsLocalRing.ResidueField ↥A) else 0) • P0 k := by
          intro k
          have h1 := congrFun (congrFun hN'N j) k
          simp only [Matrix.mul_apply, Matrix.one_apply] at h1
          rw [← h1]
        simp_rw [← Finset.sum_smul, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    ·
      rw [← hP00 l hl]
      show (∑ j, N l j • P0 j) = P0 l
      have : ∀ j, N l j • P0 j = if (j : ℕ) = 0 then P0 j else 0 := by
        intro j; rw [hN0 l j hl]; split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      have h0 : ∀ j : Fin r, ((j : ℕ) = 0) ↔ j = l := fun j => by
        constructor <;> intro h <;> [exact Fin.ext (by omega); (subst h; exact hl)]
      simp_rw [h0, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ·
      rw [hresD0 l, Finset.sum_mul, hP', map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, hres0 j, map_smul, Algebra.smul_def]
  exact ⟨⟨D', ht_basis, ht_zero, ht_inf, ht_zeroChart⟩, rfl⟩

end S_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered (solution)
