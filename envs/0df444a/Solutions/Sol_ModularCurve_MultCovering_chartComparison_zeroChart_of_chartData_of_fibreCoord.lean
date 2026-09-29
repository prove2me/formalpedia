-- Prove2me | solution 1 for ModularCurve.MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9bc8ae48-f9c3-5e73-bc61-c7536be58881

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_modulusExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_chartComparison_zeroChart_of_chartData_of_fibreCoord
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (hint0 : ∀ i, goodFamilyZero Φ.toFamData i ∈ (chart Γ 1).integers)
    (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r)
    (hrat : ∀ P ∈ (chart Γ 1).dom, P.IsRational ∧ ((chart Γ 1).placeMap P).IsRational)
    (hcQ : ∀ P ∈ (chart Γ 1).dom, (chart Γ 1).residue ⟨goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)), hint0 _⟩ ≠ 0)
    (hratio : ∀ P ∈ (chart Γ 1).dom, ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ (chart Γ 1).integers)
    (hreg : ∀ P ∈ (chart Γ 1).dom, ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ (chart Γ 1).dom, ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((chart Γ 1).placeMap P)) * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ (chart Γ 1).integers,
      ((chart Γ 1).placeMap P).ord ((chart Γ 1).residue ⟨_, hmem⟩
        - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (((chart Γ 1).placeMap P).evalAt ((chart Γ 1).residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ (chart Γ 1).dom, ∀ Q ∈ (chart Γ 1).dom, (chart Γ 1).placeMap P ≠ (chart Γ 1).placeMap Q →
      ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ (chart Γ 1).integers)
        (hmQ : ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap Q)))⁻¹ ∈ (chart Γ 1).integers),
      ∃ i j, ((chart Γ 1).placeMap P).evalAt ((chart Γ 1).residue ⟨_, hmP i⟩) * ((chart Γ 1).placeMap Q).evalAt ((chart Γ 1).residue ⟨_, hmQ j⟩)
        ≠ ((chart Γ 1).placeMap P).evalAt ((chart Γ 1).residue ⟨_, hmP j⟩) * ((chart Γ 1).placeMap Q).evalAt ((chart Γ 1).residue ⟨_, hmQ i⟩))
    (T : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → ↥(modularFunctionFieldBar (1 * p)))
    (hT : ∀ P ∈ (chart Γ 1).dom,
      ∃ h : T ((chart Γ 1).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 1).placeMap P)))
          ∈ (chart Γ 1).integers,
        (chart Γ 1).residue ⟨_, h⟩ ≠ 0 ∧ ((chart Γ 1).placeMap P).ord ((chart Γ 1).residue ⟨_, h⟩) = 1 ∧
        0 < P.ord (T ((chart Γ 1).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 1).placeMap P)))) ∧
        ∀ Q ∈ (chart Γ 1).dom, (chart Γ 1).placeMap Q = (chart Γ 1).placeMap P → Q ≠ P →
          Q.ord (T ((chart Γ 1).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 1).placeMap P)))) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ (chart Γ 1).dom, ∀ Q ∈ (chart Γ 1).dom, P ≠ Q →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        ((chart Γ 1).placeMap P = (chart Γ 1).placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (T ((chart Γ 1).placeMap P)) - Q.evalAt (T ((chart Γ 1).placeMap P))))|
            ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        ((chart Γ 1).placeMap P ≠ (chart Γ 1).placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by
  classical
  intro μ hμ hμA P hP Q hQ hPQ hnonprop
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have ht0 : ∀ i, goodFamilyZero Φ.toFamData i ≠ 0 := by
    intro i h0
    apply Φ.t_basis.1.ne_zero i
    have : goodFamilyZero Φ.toFamData i
        = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData i))⁻¹ * goodFamily Φ i := rfl
    rw [this] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (inv_ne_zero ((map_ne_zero _).2 (pow_ne_zero _ hp0)))
    · exact h1

  have hsum0 : ∀ i, s i = ∑ j, (linkMatrix Φ s hs i j * (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j)
      • goodFamilyZero Φ.toFamData j := by
    intro i
    rw [eq_sum_linkMatrix_smul_goodFamily Φ s hs i]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : goodFamilyZero Φ.toFamData j
        = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j))⁻¹ * goodFamily Φ j := rfl
    rw [this, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
      mul_inv_cancel_left₀ ((map_ne_zero _).2 (pow_ne_zero _ hp0))]

  set M' : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) :=
    fun i j => linkMatrix Φ s hs i j * (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j with hM'
  set M'inv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) :=
    fun i j => ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData i)⁻¹ * linkMatrixInv Φ s hs i j with hM'inv
  have hM'1 : M'inv * M' = 1 := by
    have h1 := linkMatrixInv_mul Φ s hs
    ext i k
    have h1ik := congrFun (congrFun h1 i) k
    simp only [Matrix.mul_apply] at h1ik ⊢
    simp only [hM', hM'inv]
    have : ∀ j, ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData i)⁻¹ * linkMatrixInv Φ s hs i j
        * (linkMatrix Φ s hs j k * (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData k)
        = ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData i)⁻¹ * (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData k
          * (linkMatrixInv Φ s hs i j * linkMatrix Φ s hs j k) := fun j => by ring
    simp_rw [this, ← Finset.mul_sum, h1ik, Matrix.one_apply]
    split_ifs with hik
    · subst hik; rw [mul_one, inv_mul_cancel₀ (pow_ne_zero _ hp0)]
    · rw [mul_zero]
  have hM'2 : M' * M'inv = 1 := by
    have h1 := linkMatrix_mul_inv Φ s hs
    ext i k
    have h1ik := congrFun (congrFun h1 i) k
    simp only [Matrix.mul_apply] at h1ik ⊢
    simp only [hM', hM'inv]
    have : ∀ j, linkMatrix Φ s hs i j * (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j
        * (((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j)⁻¹ * linkMatrixInv Φ s hs j k)
        = linkMatrix Φ s hs i j * linkMatrixInv Φ s hs j k := fun j => by
      field_simp [pow_ne_zero _ hp0]
    simp_rw [this, h1ik]
  have hMB' : ∀ i j, (p : AlgebraicClosure ℚ) ^ (linkBudget Φ s hs + modulusExp) * M' i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ (linkBudget Φ s hs + modulusExp) * M'inv i j ∈ A := by
    intro i j
    obtain ⟨h1, h2⟩ := linkBudget_spec Φ s hs A hA i j
    have hEi : hasseExp Φ.toFamData i ≤ modulusExp := hasseExp_le_modulusExp p A hA Γ Δ Φ i
    constructor
    · have : (p : AlgebraicClosure ℚ) ^ (linkBudget Φ s hs + modulusExp) * M' i j
          = (p : AlgebraicClosure ℚ) ^ modulusExp * (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j
            * ((p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j) := by
        simp only [hM']; ring
      rw [this]
      exact mul_mem (mul_mem (pow_mem hpA _) (pow_mem hpA _)) h1
    · have : (p : AlgebraicClosure ℚ) ^ (linkBudget Φ s hs + modulusExp) * M'inv i j
          = (p : AlgebraicClosure ℚ) ^ (modulusExp - hasseExp Φ.toFamData i)
            * ((p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j) := by
        simp only [hM'inv]
        rw [pow_sub₀ _ hp0 hEi, pow_add]
        ring
      rw [this]
      exact mul_mem (pow_mem hpA _) h2
  have hlink : ∀ P ∈ (chart Γ 1).dom, ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      evalVec s P = d • M'.mulVec
        (fun i => P.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹)) := by
    intro P hP
    have hr : 0 < r := Fin.pos (cQ ((chart Γ 1).placeMap P))
    exact AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s (goodFamilyZero Φ.toFamData) hs0 ht0
      M' M'inv hM'1 hM'2 hsum0 P (hrat P hP).1 (cQ ((chart Γ 1).placeMap P)) (hreg P hP)
  have hmain := AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec p hp
    (chart Γ 1) s (goodFamilyZero Φ.toFamData) hs0 hint0 cQ iQ hrat hcQ hratio hreg himm hsep
    M' M'inv hM'1 (linkBudget Φ s hs + modulusExp) hMB' hlink T hT μ hμ hμA P hP Q hQ hPQ hnonprop
  have hconst : ((4 * (linkBudget Φ s hs + modulusExp : ℕ) : ℝ)) = compConst Φ s hs := by
    rw [compConst_eq]; push_cast; ring
  rw [hconst] at hmain
  exact hmain

end S_ModularCurve_MultCovering_chartComparison_zeroChart_of_chartData_of_fibreCoord
end P2MW
export P2MW.S_ModularCurve_MultCovering_chartComparison_zeroChart_of_chartData_of_fibreCoord (solution)
