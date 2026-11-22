-- Prove2me | solution 1 for Lean4LPD.chain_le_weighted_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:06:04.474289+00:00
-- url     : https://prove2.me/submissions/d049d01c-1470-4f5b-bd61-79d0259feaf8

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Theorems.Thm_Lean4LPD_sum_reverse_choose
public import Theorems.Thm_Lean4LPD_chain_eq_zero_of_lt
public import Theorems.Thm_Lean4LPD_chain_succ_succ


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ} {C R : ℝ}
    (heps : ∀ j m, 0 ≤ eps j m) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    ∀ k m, 1 ≤ m → chain eps E (k + 1) m ≤
      C * R ^ (m - (k + 1)) * W m * ((m - 1).choose k : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    simpa using hentry m hm
  | succ k ih =>
    intro m hm
    change chain eps E (k + 2) m ≤
      C * R ^ (m - (k + 2)) * W m * ((m - 1).choose (k + 1) : ℝ)
    by_cases hk : m < k + 2
    · rw [chain_eq_zero_of_lt (k + 2) m hm hk,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    · have hkm : k + 2 ≤ m := by omega
      rw [chain_succ_succ]
      have hterm : ∀ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j) ≤
          (C * R ^ (m - (k + 2)) * W m) * ((m - j - 1).choose k : ℝ) := by
        intro j hj
        obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.mp hj
        by_cases hk' : m - j < k + 1
        · rw [chain_eq_zero_of_lt (k + 1) (m - j) (by omega) hk',
            Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
        · have hpows : R ^ (m - j - (k + 1)) * R ^ (j - 1) = R ^ (m - (k + 2)) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            eps j m * chain eps E (k + 1) (m - j) ≤
                eps j m * (C * R ^ (m - j - (k + 1)) * W (m - j) *
                  ((m - j - 1).choose k : ℝ)) :=
              mul_le_mul_of_nonneg_left (ih (m - j) (by omega)) (heps j m)
            _ = (C * R ^ (m - j - (k + 1)) * ((m - j - 1).choose k : ℝ)) *
                (eps j m * W (m - j)) := by ring
            _ ≤ (C * R ^ (m - j - (k + 1)) * ((m - j - 1).choose k : ℝ)) *
                (R ^ (j - 1) * W m) :=
              mul_le_mul_of_nonneg_left (hjump j m hj1 hjm) (by positivity)
            _ = C * (R ^ (m - j - (k + 1)) * R ^ (j - 1)) * W m *
                ((m - j - 1).choose k : ℝ) := by ring
            _ = (C * R ^ (m - (k + 2)) * W m) * ((m - j - 1).choose k : ℝ) := by
              rw [hpows]
      calc
        (∑ j ∈ Ico 1 m, eps j m * chain eps E (k + 1) (m - j)) ≤
            ∑ j ∈ Ico 1 m, (C * R ^ (m - (k + 2)) * W m) *
              ((m - j - 1).choose k : ℝ) := Finset.sum_le_sum hterm
        _ = C * R ^ (m - (k + 2)) * W m * ((m - 1).choose (k + 1) : ℝ) := by
          rw [← Finset.mul_sum, sum_reverse_choose hm k]
end Lean4LPD
