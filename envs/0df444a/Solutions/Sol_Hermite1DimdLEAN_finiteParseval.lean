-- Prove2me | solution 1 for Hermite1DimdLEAN.finiteParseval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:13:52.357796+00:00
-- url     : https://prove2.me/submissions/fbb9f3ca-b358-4a54-8b4d-07f8bf2d766d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_productBasisOrthonormal
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
private theorem gaussianInner_self
    {d : ℕ} (F : CSpace d → ℂ) :
    gaussianInner F F = ((gaussianL2NormSq F : ℝ) : ℂ) := by
  unfold gaussianInner gaussianL2NormSq
  have hfun :
      (fun z : CSpace d => F z * conj (F z)) =
        fun z : CSpace d => ((‖F z‖ ^ 2 : ℝ) : ℂ) := by
    funext z
    simpa using Complex.mul_conj' (F z)
  rw [hfun, integral_complex_ofReal]
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
private lemma gaussianInner_finite_sum_basis
    {d : ℕ} (κ β : MultiIndex d)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℂ) :
    gaussianInner (fun z => Finset.sum s (fun α => c α * PhiKappaAlpha κ α z)) (PhiKappaAlpha κ β) =
      Finset.sum s (fun α => c α * gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)) := by
  unfold gaussianInner
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro α hα
    exact (integrable_productBasis_cross κ α β).const_mul (c α)
private lemma gaussianInner_finite_sum
    {d : ℕ} (κ : MultiIndex d)
    (s t : Finset (MultiIndex d)) (a b : MultiIndex d → ℂ) :
    gaussianInner
        (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
        (fun z => Finset.sum t (fun β => b β * PhiKappaAlpha κ β z)) =
      Finset.sum t
        (fun β =>
          conj (b β) *
            gaussianInner
              (fun z => Finset.sum s (fun α => a α * PhiKappaAlpha κ α z))
              (PhiKappaAlpha κ β)) := by
  unfold gaussianInner
  have hfun :
      (fun z : CSpace d =>
        (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
          conj (Finset.sum t (fun β => b β * PhiKappaAlpha κ β z))) =
        fun z : CSpace d =>
          Finset.sum t
            (fun β =>
              conj (b β) *
                ((Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
                  conj (PhiKappaAlpha κ β z))) := by
    funext z
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    simp [mul_assoc, mul_comm]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro β hβ
    have hsumInt :
        Integrable
          (fun z : CSpace d =>
            (Finset.sum s (fun α => a α * PhiKappaAlpha κ α z)) *
              conj (PhiKappaAlpha κ β z))
          (gaussianMeasure d) := by
      simp_rw [Finset.sum_mul, mul_assoc]
      exact MeasureTheory.integrable_finsetSum _ fun α _ =>
        (integrable_productBasis_cross κ α β).const_mul (a α)
    exact (hsumInt.const_mul (conj (b β)))
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
    {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) :
    hermiteNormSq κ G = Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 := by
  /-
  Scaffolding guidance:
  keep the public statement on literal finite coefficient families.
  This is the version later files regroup by blocks and total degree.
  -/
  classical
  have hinner :
      gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ G) =
        Finset.sum G.support fun α => G.coeff α * conj (G.coeff α) := by
    unfold evalHermiteSum
    rw [gaussianInner_finite_sum (κ := κ) (s := G.support) (t := G.support)
      (a := G.coeff) (b := G.coeff)]
    calc
      ∑ β ∈ G.support,
          conj (G.coeff β) *
            gaussianInner (fun z => ∑ α ∈ G.support, G.coeff α * PhiKappaAlpha κ α z)
              (PhiKappaAlpha κ β)
          = ∑ β ∈ G.support,
              conj (G.coeff β) *
                ∑ α ∈ G.support, G.coeff α * gaussianInner (PhiKappaAlpha κ α) (PhiKappaAlpha κ β)
                    := by
                  refine Finset.sum_congr rfl ?_
                  intro β hβ
                  rw [gaussianInner_finite_sum_basis (κ := κ) (β := β)
                    (s := G.support) (c := G.coeff)]
      _ = ∑ α ∈ G.support, G.coeff α * conj (G.coeff α) := by
            refine Finset.sum_congr rfl fun β hβ => ?_
            rw [Finset.sum_eq_single β]
            · simp [productBasisOrthonormal, mul_comm]
            · intro α hα hne
              simp [productBasisOrthonormal, hne]
            · exact fun hnotin => absurd hβ hnotin
  unfold hermiteNormSq
  apply Complex.ofReal_injective
  rw [← gaussianInner_self, hinner]
  simp [Complex.mul_conj']
end Hermite1DimdLEAN
