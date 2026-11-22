-- Prove2me | solution 1 for Lean4LPD.total_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:13.076881+00:00
-- url     : https://prove2.me/submissions/9b4f25e5-36d1-45e9-a470-5889eab0021f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Theorems.Thm_Lean4LPD_tZeroModel_pos
public import Theorems.Thm_Lean4LPD_cZero_le_two
public import Theorems.Thm_Lean4LPD_prod_rungW_eq


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
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1)
          * (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
          / (Nat.factorial (m + 1) : ℝ) * M := by
  obtain ⟨_, _, hG, _, _⟩ := id hadm
  have hc2 : cZero (r : ℝ) (m : ℝ) G B ≤ 2 := cZero_le_two hadm hm1 hr5 hB0 hB1
  have hcpos : 0 ≤ cZero (r : ℝ) (m : ℝ) G B := by
    unfold cZero
    have h3 : (0 : ℝ) < (1 + B) ^ ((1 : ℝ) / ((m : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith) _
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    positivity
  have hfac : (0 : ℝ) < (Nat.factorial (m + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + 1)
  have hprodpos : (0 : ℝ) ≤ ∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c) := by
    refine Finset.prod_nonneg fun i _ => ?_
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  -- t₀ from model parameters, and the identity 2*G*a = (1/t₀)/kh1
  have ht0 : tZeroModel G (kh1 + 1) a = 1 / (2 * G * kh1 * a) := by
    unfold tZeroModel; norm_num
  have ht0pos : 0 < tZeroModel G (kh1 + 1) a := tZeroModel_pos hG (by linarith) ha
  have hbase : decayBase G (kh1 + 1) a t = 2 * G * kh1 * a * t := by
    have hne : (2 : ℝ) * G * kh1 * a ≠ 0 := by positivity
    unfold decayBase
    rw [ht0]
    field_simp
  -- step 1: replace c₀ by 2
  have h1 : (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1) ≤ (2 * G * a * t) ^ (m + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [hc2, hG.le, ha.le, ht, mul_nonneg (mul_nonneg hG.le ha.le) ht]
  -- step 2: the rung product, and the exact cancellation of kh1^(m+1)
  have h2 : (2 * G * a * t) ^ (m + 1) * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
      = decayBase G (kh1 + 1) a t ^ (m + 1) * ∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c) := by
    rw [prod_rungW_eq, hbase]
    rw [show (2 : ℝ) * G * kh1 * a * t = (2 * G * a * t) * kh1 by ring, mul_pow]
    ring
  have hcoef : (0 : ℝ) ≤ M / (Nat.factorial (m + 1) : ℝ) := by positivity
  have hrw : (0 : ℝ) ≤ ∏ j ∈ range (m + 1), rungW kh1 c (j + 2) := by
    rw [prod_rungW_eq]
    have : (0 : ℝ) ≤ kh1 ^ (m + 1) := by positivity
    exact mul_nonneg this hprodpos
  have hAP := mul_le_mul_of_nonneg_right h1 hrw
  calc S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
            * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
            / (Nat.factorial (m + 1) : ℝ) * M := hstep
    _ = ((cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
            * ∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
          * (M / (Nat.factorial (m + 1) : ℝ)) := by ring
    _ ≤ ((2 * G * a * t) ^ (m + 1) * ∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
          * (M / (Nat.factorial (m + 1) : ℝ)) := mul_le_mul_of_nonneg_right hAP hcoef
    _ = (decayBase G (kh1 + 1) a t ^ (m + 1) * ∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
          * (M / (Nat.factorial (m + 1) : ℝ)) := by rw [h2]
    _ = decayBase G (kh1 + 1) a t ^ (m + 1)
            * (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
            / (Nat.factorial (m + 1) : ℝ) * M := by ring
end Lean4LPD
