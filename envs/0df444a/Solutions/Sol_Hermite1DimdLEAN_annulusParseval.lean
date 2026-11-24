-- Prove2me | solution 1 for Hermite1DimdLEAN.annulusParseval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:31.525604+00:00
-- url     : https://prove2.me/submissions/0e4294c6-49b3-4dff-bb44-5c431b40c59c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_annulusOrthogonality
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
private theorem annulusInner_self
    {d : ℕ} (j : MultiIndex d) (F : CSpace d → ℂ) :
    annulusInner j F F = ((annulusMass j F : ℝ) : ℂ) := by
  classical
  unfold annulusInner annulusMass
  have hfun :
      (fun z : CSpace d => if z ∈ productAnnulus j then F z * conj (F z) else 0) =
        fun z : CSpace d => ((if z ∈ productAnnulus j then ‖F z‖ ^ 2 else 0 : ℝ) : ℂ) := by
    funext z
    split_ifs with hz <;> simp [Complex.mul_conj']
  rw [hfun, integral_complex_ofReal]
private lemma annulusInner_finite_sum_basis
    {d : ℕ} (j κ β : MultiIndex d)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℂ) :
    annulusInner j (fun z => Finset.sum s (fun α => c α * PhiKappaAlpha κ α z)) (PhiKappaAlpha κ
        β) =
      Finset.sum s (fun α => c α * annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)) := by
  classical
  unfold annulusInner
  change
    ∫ z : CSpace d,
      if z ∈ productAnnulus j then
        (∑ α ∈ s, c α * PhiKappaAlpha κ α z) * conj (PhiKappaAlpha κ β z)
      else 0 ∂ gaussianMeasure d =
      Finset.sum s (fun α =>
        c α * ∫ z : CSpace d,
          if z ∈ productAnnulus j then
            PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)
          else 0 ∂ gaussianMeasure d)
  have hsum :
      (fun z : CSpace d =>
        if z ∈ productAnnulus j then
          (∑ α ∈ s, c α * PhiKappaAlpha κ α z) * conj (PhiKappaAlpha κ β z)
        else 0) =
        (fun z : CSpace d =>
          Finset.sum s (fun α =>
            if z ∈ productAnnulus j then
              c α * (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
            else 0)) := by
    funext z
    by_cases hz : z ∈ productAnnulus j
    · rw [if_pos hz, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro α hα
      simp [hz, mul_assoc]
    · simp [hz]
  rw [hsum, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    simp_all
  · intro α hα
    simpa [indicatorMul, Set.indicator, mul_assoc] using
      ((integrable_productBasis_cross κ α β).indicator (measurableSet_productAnnulus j)).const_mul
        (c α)
private lemma annulusInner_finite_sum
    {d : ℕ} (j κ : MultiIndex d)
    (s t : Finset (MultiIndex d))
    (a b : MultiIndex d → ℂ) :
    annulusInner j
        (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
        (fun z => Finset.sum t (fun β => b β * PhiKappaAlpha κ β z)) =
      Finset.sum t (fun β =>
        conj (b β) *
          annulusInner j
            (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
            (PhiKappaAlpha κ β)) := by
  classical
  unfold annulusInner
  change
    ∫ z : CSpace d,
      if z ∈ productAnnulus j then
        (∑ α ∈ s, a α * PhiKappaAlpha κ α z) *
          conj (∑ β ∈ t, b β * PhiKappaAlpha κ β z)
      else 0 ∂ gaussianMeasure d =
      Finset.sum t (fun β =>
        conj (b β) *
          ∫ z : CSpace d,
            if z ∈ productAnnulus j then
              (∑ α ∈ s, a α * PhiKappaAlpha κ α z) *
                conj (PhiKappaAlpha κ β z)
            else 0 ∂ gaussianMeasure d)
  have hrewrite :
      (fun z : CSpace d =>
        (if z ∈ productAnnulus j then
          (∑ α ∈ s, a α * PhiKappaAlpha κ α z) *
            conj (∑ β ∈ t, b β * PhiKappaAlpha κ β z)
        else 0)) =
        (fun z : CSpace d =>
          Finset.sum t fun β =>
            if z ∈ productAnnulus j then
              conj (b β) *
                ((Finset.sum s fun α => a α * PhiKappaAlpha κ α z) *
                  conj (PhiKappaAlpha κ β z))
            else 0) := by
    funext z
    by_cases hz : z ∈ productAnnulus j
    · rw [if_pos hz, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp [hz, mul_assoc, mul_comm]
    · simp [hz]
  rw [hrewrite, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [← MeasureTheory.integral_const_mul]
    simp_all
  · intro β hβ
    have hsum :
        (fun z : CSpace d =>
          if z ∈ productAnnulus j then
            conj (b β) *
              ((Finset.sum s fun α => a α * PhiKappaAlpha κ α z) *
                conj (PhiKappaAlpha κ β z))
          else 0) =
          (fun z : CSpace d =>
            Finset.sum s fun α =>
              if z ∈ productAnnulus j then
                (conj (b β) * a α) *
                  (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z))
              else 0) := by
      funext z
      by_cases hz : z ∈ productAnnulus j
      · simp [hz, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      · simp [hz]
    rw [hsum]
    refine MeasureTheory.integrable_finsetSum _ ?_
    intro α hα
    refine (((integrable_productBasis_cross κ α β).indicator (measurableSet_productAnnulus j)).const_mul
      (conj (b β) * a α)).congr ?_
    filter_upwards with z
    symm
    by_cases hz : z ∈ productAnnulus j
    · simp [Set.indicator, hz, mul_left_comm, mul_comm]
    · simp [Set.indicator, hz]
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
    {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d) (G : FiniteHermiteSum d) :
    annulusMass j (evalHermiteSum κ G) =
      Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 * annulusMass j (PhiKappaAlpha κ α) := by
  classical
  have hinner :
      annulusInner j (evalHermiteSum κ G) (evalHermiteSum κ G) =
        Finset.sum G.support
          (fun α => G.coeff α * conj (G.coeff α) * ((annulusMass j (PhiKappaAlpha κ α) : ℝ) : ℂ))
              := by
    unfold evalHermiteSum
    rw [annulusInner_finite_sum (j := j) (κ := κ) (s := G.support) (t := G.support)
      (a := G.coeff) (b := G.coeff)]
    calc
      ∑ β ∈ G.support,
          conj (G.coeff β) *
            annulusInner j (fun z => ∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z)
              (PhiKappaAlpha κ β)
          = ∑ β ∈ G.support,
              conj (G.coeff β) *
                ∑ α ∈ G.support, G.coeff α * annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ
                    β) := by
                  refine Finset.sum_congr rfl ?_
                  intro β hβ
                  rw [annulusInner_finite_sum_basis (j := j) (κ := κ) (β := β)
                    (s := G.support) (c := G.coeff)]
      _ = ∑ α ∈ G.support,
            G.coeff α * conj (G.coeff α) * ((annulusMass j (PhiKappaAlpha κ α) : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl fun β hβ => ?_
              rw [Finset.sum_eq_single β]
              · simp [annulusInner_self, mul_comm, mul_left_comm]
              · intro α hα hne
                simp [annulusOrthogonality, hne]
              · exact fun hnotin => absurd hβ hnotin
  apply Complex.ofReal_injective
  rw [← annulusInner_self, hinner]
  simp [Complex.mul_conj', mul_comm]
end Hermite1DimdLEAN
