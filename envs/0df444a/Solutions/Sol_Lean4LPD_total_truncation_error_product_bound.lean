-- Prove2me | solution 1 for Lean4LPD.total_truncation_error_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:08.620509+00:00
-- url     : https://prove2.me/submissions/0087ca6d-3c11-4d7d-be8b-04a1abb6f989

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_prod_add_one_le_factorial_exp_rpow
public import Theorems.Thm_Lean4LPD_chainWeight_zero
public import Theorems.Thm_Lean4LPD_decayBase_nonneg
public import Theorems.Thm_Lean4LPD_total_truncation_error
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {S M t a G kh1 c B : ℝ} {m r : ℕ}
    (hstep : S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
              * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
              / (Nat.factorial (m + 1) : ℝ) * M)
    (hadm : Admissible (r : ℝ) (m : ℝ) G) (hm1 : 1 ≤ (m : ℝ)) (hr5 : 5 ≤ (r : ℝ))
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh1 : 0 < kh1) (hc : 0 ≤ c)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) :
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
      (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M := by
  have htotal := total_truncation_error hstep hadm hm1 hr5 hB0 hB1 hkh1 hc ha ht hM
  have hfac : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by positivity
  have hprod : (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c)) /
      (Nat.factorial (m + 1) : ℝ) ≤ (Real.exp 1 * ((m : ℝ) + 1)) ^ c := by
    apply (div_le_iff₀ hfac).mpr
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using
      prod_add_one_le_factorial_exp_rpow hc (m + 1) (by omega)
  obtain ⟨_, _, hG, _, _⟩ := hadm
  have hbase : 0 ≤ decayBase G (kh1 + 1) a t ^ (m + 1) :=
    pow_nonneg (decayBase_nonneg hG (by linarith) ha ht) _
  calc
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
        (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c)) /
        (Nat.factorial (m + 1) : ℝ) * M := htotal
    _ = (decayBase G (kh1 + 1) a t ^ (m + 1) *
        ((∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c)) /
          (Nat.factorial (m + 1) : ℝ))) * M := by ring
    _ ≤ decayBase G (kh1 + 1) a t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ c * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hbase) hM
end Lean4LPD
