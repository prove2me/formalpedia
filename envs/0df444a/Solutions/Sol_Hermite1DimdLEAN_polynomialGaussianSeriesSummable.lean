-- Prove2me | solution 1 for Hermite1DimdLEAN.polynomialGaussianSeriesSummable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:29.457949+00:00
-- url     : https://prove2.me/submissions/efd642df-bbc3-424d-838a-2c53f286c67c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Theorems.Thm_HermiteLEAN_polynomial_times_gaussian_le_gaussian
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma summable_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun r : ℕ => Real.exp (-a * (r : ℝ) ^ 2)) := by
  refine Real.summable_exp_nat_mul_of_ge ?_ ?_
  · linarith only [ha]
  · intro i
    have hreal : (i : ℝ) ≤ (i : ℝ) * (i : ℝ) := by exact_mod_cast Nat.le_mul_self i
    simpa [pow_two] using hreal
private lemma polynomialGaussianTailMajorant_summable
    {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Summable (fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2)) := by
  obtain ⟨C, hCpos, hbound⟩ :=
    HermiteLEAN.polynomial_times_gaussian_le_gaussian ha k
  exact Summable.of_nonneg_of_le
      (f := fun r : ℕ => C * Real.exp (-(a / 2) * (r : ℝ) ^ 2))
      (g := fun r : ℕ => (1 + (r : ℝ) ^ k) * Real.exp (-a * (r : ℝ) ^ 2))
      (fun r => by positivity)
      (fun r => hbound (r : ℝ) (by positivity))
      ((summable_exp_neg_mul_sq (by linarith only [ha])).mul_left C)
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
    (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Summable (fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * r ^ 2)) :=
  Summable.of_nonneg_of_le
    (f := fun r : ℕ => (1 + (r : ℝ) ^ m) * Real.exp (-c * (r : ℝ) ^ 2))
    (g := fun r : ℕ => (r : ℝ) ^ m * Real.exp (-c * (r : ℝ) ^ 2))
    (fun r => by positivity)
    (fun r => mul_le_mul_of_nonneg_right (by linarith only []) (by positivity))
    (polynomialGaussianTailMajorant_summable hc m)
end Hermite1DimdLEAN
