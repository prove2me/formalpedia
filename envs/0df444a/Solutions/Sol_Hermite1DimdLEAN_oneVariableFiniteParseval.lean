-- Prove2me | solution 1 for Hermite1DimdLEAN.oneVariableFiniteParseval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:13.637292+00:00
-- url     : https://prove2.me/submissions/6a5c0511-8dad-47a3-be6f-c840457f1ea7

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_Hermite1DimdLEAN_oneVariableBasisOrthonormal
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
private lemma measurable_ofReal_gaussianDensity (d : ℕ) :
    Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z)) := by
  unfold gaussianDensity
  fun_prop
private lemma gaussianDensity_ofReal_lt_top (d : ℕ) :
    ∀ᵐ x : CSpace d, ENNReal.ofReal (gaussianDensity d x) < ⊤ := by
  simp_all
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
    simp [mul_assoc]
  · exact measurable_ofReal_gaussianDensity 1
  · exact gaussianDensity_ofReal_lt_top 1
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
private lemma integrable_oneDimBasis_cross
    (k : ℕ) (α β : MultiIndex 1) :
    Integrable
      (fun z : CSpace 1 =>
        oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z))
      (gaussianMeasure 1) := by
  exact integrable_oneDimPhi_cross_gaussian k (α 0) (β 0)
private lemma gaussianInner_finite_sum_basis_one
    (k : ℕ) (β : MultiIndex 1)
    (s : Finset (MultiIndex 1)) (c : MultiIndex 1 → ℂ) :
    gaussianInner
        (fun z : CSpace 1 => Finset.sum s (fun α => c α * oneDimLift (oneDimPhi k (α 0)) z))
        (oneDimLift (oneDimPhi k (β 0))) =
      Finset.sum s
        (fun α =>
          c α *
            gaussianInner (d := 1) (oneDimLift (oneDimPhi k (α 0))) (oneDimLift (oneDimPhi k (β
                0)))) := by
  unfold gaussianInner
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro α hα
    exact
      (MeasureTheory.integral_const_mul (c α)
        (fun z : CSpace 1 =>
          oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z)))
  · intro α hα
    exact (integrable_oneDimBasis_cross k α β).const_mul (c α)
private lemma gaussianInner_finite_sum_one
    (k : ℕ)
    (s t : Finset (MultiIndex 1)) (a b : MultiIndex 1 → ℂ) :
    gaussianInner
        (fun z : CSpace 1 => Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z))
        (fun z : CSpace 1 => Finset.sum t (fun β => b β * oneDimLift (oneDimPhi k (β 0)) z)) =
      Finset.sum t
        (fun β =>
          conj (b β) *
            gaussianInner
              (fun z : CSpace 1 => Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z))
              (oneDimLift (oneDimPhi k (β 0)))) := by
  unfold gaussianInner
  have hfun :
      (fun z : CSpace 1 =>
        (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
          conj (Finset.sum t (fun β => b β * oneDimLift (oneDimPhi k (β 0)) z))) =
        fun z : CSpace 1 =>
          Finset.sum t
            (fun β =>
              conj (b β) *
                ((Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
                  conj (oneDimLift (oneDimPhi k (β 0)) z))) := by
    funext z
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    simp [mul_assoc, mul_comm]
  rw [hfun, MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro β hβ
    exact
      (MeasureTheory.integral_const_mul (conj (b β))
        (fun z : CSpace 1 =>
          (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
            conj (oneDimLift (oneDimPhi k (β 0)) z)))
  · intro β hβ
    have hsumInt :
        Integrable
          (fun z : CSpace 1 =>
            (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
              conj (oneDimLift (oneDimPhi k (β 0)) z))
          (gaussianMeasure 1) := by
      rw [show (fun z : CSpace 1 =>
          (Finset.sum s (fun α => a α * oneDimLift (oneDimPhi k (α 0)) z)) *
            conj (oneDimLift (oneDimPhi k (β 0)) z)) =
          fun z : CSpace 1 =>
            Finset.sum s
              (fun α => a α *
                (oneDimLift (oneDimPhi k (α 0)) z * conj (oneDimLift (oneDimPhi k (β 0)) z))) by
            funext z
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro α hα
            ring]
      refine MeasureTheory.integrable_finsetSum _ (fun α hα => ?_)
      exact (integrable_oneDimBasis_cross k α β).const_mul (a α)
    exact hsumInt.const_mul (conj (b β))
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
    (k : ℕ) (G : FiniteHermiteSum 1) :
    hermiteNormSq (d := 1) (fun _ => k) G =
      Finset.sum G.support fun n => ‖G.coeff n‖ ^ 2 := by
  /-
  Scaffolding guidance:
  keep this finite and coefficient-facing; no closure language is needed by
  the higher-dimensional files.
  -/
  classical
  have heval :
      evalHermiteSum (fun _ => k) G =
        (fun z : CSpace 1 =>
          Finset.sum G.support (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z)) := by
    funext z
    simp [evalHermiteSum, PhiKappaAlpha, oneDimLift]
  have hinner :
      gaussianInner (evalHermiteSum (fun _ => k) G) (evalHermiteSum (fun _ => k) G) =
        Finset.sum G.support fun α => G.coeff α * conj (G.coeff α) := by
    calc
      gaussianInner (evalHermiteSum (fun _ => k) G) (evalHermiteSum (fun _ => k) G) =
        gaussianInner
          (fun z : CSpace 1 =>
            Finset.sum G.support (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z))
          (fun z : CSpace 1 =>
            Finset.sum G.support (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z)) := by
              simpa using congrArg₂ gaussianInner heval heval
      _ = Finset.sum G.support
            (fun α => G.coeff α * conj (G.coeff α)) := by
        rw [gaussianInner_finite_sum_one (k := k) (s := G.support) (t := G.support)
          (a := G.coeff) (b := G.coeff)]
        calc
      Finset.sum G.support
        (fun β =>
          conj (G.coeff β) *
            gaussianInner
              (fun z =>
                Finset.sum G.support
                  (fun α => G.coeff α * oneDimLift (oneDimPhi k (α 0)) z))
              (oneDimLift (oneDimPhi k (β 0)))) =
        Finset.sum G.support
          (fun β =>
            conj (G.coeff β) *
            Finset.sum G.support
              (fun α =>
                G.coeff α *
                gaussianInner
                  (oneDimLift (oneDimPhi k (α 0)))
                  (oneDimLift (oneDimPhi k (β 0))))) := by
            refine Finset.sum_congr rfl ?_
            intro β hβ
            rw [gaussianInner_finite_sum_basis_one (k := k) (β := β)
              (s := G.support) (c := G.coeff)]
        _ =
          Finset.sum G.support (fun β => conj (G.coeff β) * G.coeff β) := by
            refine Finset.sum_congr rfl ?_
            intro β hβ
            rw [Finset.sum_eq_single β]
            · simp [oneVariableBasisOrthonormal]
            · intro α hα hne
              have hne0 : α 0 ≠ β 0 := by
                intro h0
                apply hne
                ext q
                fin_cases q
                simpa using h0
              simp [oneVariableBasisOrthonormal, hne0]
            · simp_all
        _ = Finset.sum G.support (fun α => G.coeff α * conj (G.coeff α)) := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            ring
  unfold hermiteNormSq
  apply Complex.ofReal_injective
  calc
    (((gaussianL2NormSq (evalHermiteSum (fun _ => k) G) : ℝ)) : ℂ)
        = gaussianInner (evalHermiteSum (fun _ => k) G) (evalHermiteSum (fun _ => k) G) :=
          (gaussianInner_self (F := evalHermiteSum (fun _ => k) G)).symm
    _ = Finset.sum G.support (fun α => G.coeff α * conj (G.coeff α)) := hinner
    _ = (((Finset.sum G.support fun α => ‖G.coeff α‖ ^ 2 : ℝ)) : ℂ) := by simp [Complex.mul_conj']
end Hermite1DimdLEAN
