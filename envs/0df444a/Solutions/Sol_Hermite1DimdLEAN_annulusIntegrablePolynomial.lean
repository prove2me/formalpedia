-- Prove2me | solution 1 for Hermite1DimdLEAN.annulusIntegrablePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:38.695286+00:00
-- url     : https://prove2.me/submissions/8ab1b1a8-1092-4b74-8e8a-2956956bfb6e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_tensorGaussianFactorization
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_integrable_weightedCross
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma integrable_oneDimPhi_cross_gaussian
    (k m n : ℕ) :
    Integrable
      (fun z : CSpace 1 => oneDimPhi k m (z 0) * conj (oneDimPhi k n (z 0)))
      (gaussianMeasure 1) := by
  change
    Integrable
      (fun z : CSpace 1 => HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
      (gaussianMeasure 1)
  rw [gaussianMeasure, MeasureTheory.integrable_withDensity_iff_integrable_smul']
  · have hcross :
        Integrable
          (fun z : CSpace 1 =>
            HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)) *
              (Real.exp (-‖z 0‖ ^ 2) : ℂ)) := by
      have h :=
        (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integrable_comp_of_integrable
          (g := fun z : ℂ =>
            HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z) *
              (Real.exp (-‖z‖ ^ 2) : ℂ))
          (HermitekLEAN.integrable_weightedCross k m n)
      refine h.congr ?_
      filter_upwards with z
      rfl
    have hsmul :
        Integrable
          (fun z : CSpace 1 =>
            Real.exp (-‖z 0‖ ^ 2) •
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      convert hcross using 1
      funext z
      simp [Algebra.smul_def, mul_left_comm, mul_comm]
    refine (hsmul.const_mul (1 / Real.pi)).congr ?_
    filter_upwards with z
    symm
    have hnonneg : 0 ≤ π⁻¹ * rexp (-‖z 0‖ ^ 2) := by positivity
    simp only [gaussianDensity, pow_one, one_div, univ_unique, Fin.default_eq_zero, Fin.isValue,
      sum_singleton, hnonneg, ENNReal.toReal_ofReal, real_smul, ofReal_exp, ofReal_neg, ofReal_pow]
    have hleft :
        (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
          (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
      simp [Algebra.smul_def]
    calc
      (π⁻¹ * rexp (-‖z 0‖ ^ 2)) •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) =
        (((π⁻¹ * rexp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := hleft
      _ = (↑π)⁻¹ * (cexp (-↑‖z 0‖ ^ 2) *
            (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))) := by
          simp [mul_assoc, mul_left_comm]
  · change
      Measurable
        (fun z : CSpace 1 =>
          ENNReal.ofReal ((1 / Real.pi ^ 1) * Real.exp (-(∑ q : Fin 1, ‖z q‖ ^ 2))))
    fun_prop
  · simp
private lemma integrable_productBasis_cross
    {d : ℕ} (κ α β : MultiIndex d) :
    Integrable
      (fun z : CSpace d => PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
      (gaussianMeasure d) := by
  simpa [PhiKappaAlpha, Finset.prod_mul_distrib, mul_assoc, mul_left_comm, mul_comm] using
    (tensorGaussianFactorization d
      (fun q z => oneDimPhi (κ q) (α q) z)
      (fun q z => oneDimPhi (κ q) (β q) z)
      (fun q => by
        simpa [oneDimLift] using
          integrable_oneDimPhi_cross_gaussian (κ q) (α q) (β q))).1
private lemma measurableSet_productAnnulus
    {d : ℕ} (j : MultiIndex d) :
    MeasurableSet (productAnnulus j) := by
  classical
  have h :
      MeasurableSet (⋂ q : Fin d, {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (f := fun q : Fin d => {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ <
        (j q : ℝ) + 1}) ?_
    intro q
    have hge : MeasurableSet {z : CSpace d | (j q : ℝ) ≤ ‖z q‖} :=
      measurableSet_le measurable_const (measurable_norm.comp (continuous_apply q).measurable)
    have hlt : MeasurableSet {z : CSpace d | ‖z q‖ < (j q : ℝ) + 1} :=
      measurableSet_lt (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.ofPred_and] using hge.inter hlt
  simpa [productAnnulus, Set.ofPred_forall] using h
private lemma integrable_evalHermiteSum_cross
    {d : ℕ} (κ : MultiIndex d) (G H : FiniteHermiteSum d) :
    Integrable
      (fun z : CSpace d => evalHermiteSum κ G z * conj (evalHermiteSum κ H z))
      (gaussianMeasure d) := by
  classical
  unfold evalHermiteSum
  have hrewrite :
      (fun z : CSpace d =>
        (∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z) *
          conj (∑ β ∈ H.support, H.coeff β * PhiKappaAlpha κ β z)) =
        (fun z : CSpace d =>
          ∑ α ∈ G.support,
            ∑ β ∈ H.support,
              G.coeff α * conj (H.coeff β) *
                (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))) := by
    funext z
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [map_sum, mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hrewrite]
  refine MeasureTheory.integrable_finsetSum _ ?_
  intro α hα
  refine MeasureTheory.integrable_finsetSum _ ?_
  intro β hβ
  exact
    (integrable_productBasis_cross κ α β).const_mul (G.coeff α * conj (H.coeff β))
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (j κ : MultiIndex d) (G H : FiniteHermiteSum d) :
    Integrable
      (indicatorMul (productAnnulus j)
        (fun z => evalHermiteSum κ G z * conj (evalHermiteSum κ H z)))
      (gaussianMeasure d) := by
  refine ((integrable_evalHermiteSum_cross κ G H).indicator
    (measurableSet_productAnnulus j)).congr ?_
  filter_upwards with z
  rfl
end Hermite1DimdLEAN
