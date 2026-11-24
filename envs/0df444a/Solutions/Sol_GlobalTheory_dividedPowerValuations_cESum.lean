-- Prove2me | solution 1 for GlobalTheory.dividedPowerValuations_cESum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:36:04.020291+00:00
-- url     : https://prove2.me/submissions/38ac120d-81ed-45dd-97db-89184a990d3f

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CmValuesExponentLogSumLe
import Theorems.Thm_GlobalTheory_ceSum_val_le
import Theorems.Thm_GlobalTheory_ceSum_small_le
import Theorems.Thm_GlobalTheory_ceSum_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.PairingDivisionLocalBalance.CESum := by
  intro f X S hX hfX hS
  have hX0 : X ≠ 0 := by omega
  have hsum := Finset.sum_le_sum fun l hl => ceSum_term_le f X l hX0 (hS l hl)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hv := ceSum_val_le S hS X
  have hs := ceSum_small_le S hS (X / 2 + 1)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX
  have hL0 : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hA : ∑ l ∈ S, (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
      ≤ ((f : ℝ) + 2) * Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hB : ∑ l ∈ S, (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
      ≤ Real.log ((X : ℝ) + 1) := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hL0
  have hlogX : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL4 : 4 * Real.log 2 ≤ Real.log ((X : ℝ) + 1) := by
    have : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hn : (((X / 2 + 1 : ℕ)) : ℝ) * 2 ≤ X + 2 := by
    have : (X / 2 + 1) * 2 ≤ X + 2 := by omega
    exact_mod_cast this
  have hf : (f : ℝ) * 2 ≤ X := by exact_mod_cast (by omega : f * 2 ≤ X)
  rw [h4] at hs
  have p1 : 0 ≤ ((X : ℝ) - 2 * f) * Real.log 2 := mul_nonneg (by linarith) hlog2
  have p2 : 0 ≤ ((X : ℝ) + 2 - ((X / 2 + 1 : ℕ) : ℝ) * 2) * Real.log 2 :=
    mul_nonneg (by linarith) hlog2
  have p3 : 0 ≤ ((X : ℝ) - 2) * (Real.log ((X : ℝ) + 1) - 4 * Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  have p4 : 0 ≤ ((X : ℝ) - 16) * Real.log 2 := mul_nonneg (by linarith) hlog2
  nlinarith
end GlobalTheory
