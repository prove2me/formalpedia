-- Prove2me | solution 1 for IntMul.HvdH.clocked_recursive_multiplier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T15:03:11.501327+00:00
-- url     : https://prove2.me/submissions/907ef1a2-9f91-43b4-9bf3-2ab456ecd1f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_HvdH_StepParameters
import Theorems.Thm_IntMul_multipliesAt_sInf
import Theorems.Thm_IntMul_Kappa_jain_round6
import Mathlib.Tactic

open scoped BigOperators
open IntMul

namespace IntMul.HvdH.ClockedSupport

lemma budget_nonneg {M : MultitapeTM} {n : ℕ} {τ : ℝ}
    (h : MultipliesAt M n τ) : 0 ≤ τ := by
  obtain ⟨t, ht, _⟩ := h (List.replicate n false) (List.replicate n false)
    (by simp) (by simp)
  exact (Nat.cast_nonneg t).trans ht

lemma budget_mono {M : MultitapeTM} {n : ℕ} {τ τ' : ℝ}
    (h : MultipliesAt M n τ) (hle : τ ≤ τ') : MultipliesAt M n τ' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hle, hh⟩

lemma lg_le_log (n : ℕ) (hn : 2 ≤ n) :
    (lg n : ℝ) ≤ (2 / Real.log 2) * Real.log n := by
  have hb : 1 ≤ Nat.clog 2 n := by
    have hh := Nat.clog_mono_right 2 hn
    rwa [show Nat.clog 2 2 = 1 by decide] at hh
  have hlg : lg n = Nat.clog 2 n := max_eq_left hb
  have hpow := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num)
    (show 1 < n by omega)
  have hpowR : (2 : ℝ) ^ ((Nat.clog 2 n) - 1) < n := by
    exact_mod_cast hpow
  have hlogs := Real.log_lt_log (by positivity) hpowR
  rw [Real.log_pow] at hlogs
  have hcast : (((Nat.clog 2 n - 1 : ℕ) : ℝ)) = (Nat.clog 2 n : ℝ) - 1 := by
    rw [Nat.cast_sub hb, Nat.cast_one]
  rw [hcast] at hlogs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [hlg]
  calc
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.log n / Real.log 2 := by
      apply (le_div_iff₀ hlog2).mpr
      nlinarith
    _ = (2 / Real.log 2) * Real.log n := by ring

end IntMul.HvdH.ClockedSupport

/-- Conditional implication: it supplies no multiplication machine without `hbound`. -/
theorem IntMul.HvdH.clocked_recursive_multiplier_of_kappa_bound
    (κ : ℝ) (hκ : 0 ≤ κ) (hbound : KappaBound κ) (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : MultitapeTM,
      (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n b p T r : ℕ, IntMul.HvdH.StepParameters d n b p T r →
        ∀ τ : ℝ, MultipliesAt M (3 * r * p) τ →
          MultipliesAt M n
            (12 * (T : ℝ) / r * τ + C * ((n : ℝ) * Real.log n)) := by
  classical
  rcases hbound with ⟨M, hcorrect, c, hc, n₀, hlarge⟩
  let A : ℝ := 2 * c / Real.log 2
  have hbudget_large (n : ℕ) (hn₀ : n₀ ≤ n) (hn : 2 ≤ n) :
      MultipliesAt M n (A * ((n : ℝ) * Real.log n)) := by
    have hlg : (1 : ℝ) ≤ lg n := by
      exact_mod_cast (show 1 ≤ lg n from le_max_right _ _)
    have hrpow : (lg n : ℝ) ^ (1 - κ) ≤ (lg n : ℝ) := by
      calc
        (lg n : ℝ) ^ (1 - κ) ≤ (lg n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlg (by linarith)
        _ = (lg n : ℝ) := Real.rpow_one _
    apply ClockedSupport.budget_mono (hlarge n hn₀ (by omega))
    calc
      c * ((n : ℝ) * (lg n : ℝ) ^ (1 - κ)) ≤ c * ((n : ℝ) * lg n) := by
        gcongr
      _ ≤ c * ((n : ℝ) * ((2 / Real.log 2) * Real.log n)) := by
        gcongr
        exact ClockedSupport.lg_le_log n hn
      _ = A * ((n : ℝ) * Real.log n) := by dsimp [A]; ring
  let W : ℕ → ℝ := fun n => sInf {τ : ℝ | MultipliesAt M n τ}
  let D : ℕ → ℝ := fun n => max 0 (W n / ((n : ℝ) * Real.log n))
  let S : ℝ := ∑ i ∈ Finset.range n₀, D i
  let C : ℝ := max A S
  have hW (n : ℕ) (hn : 1 ≤ n) : MultipliesAt M n (W n) :=
    IntMul.multipliesAt_sInf (hcorrect n hn)
  have huniform (n : ℕ) (hn : 2 ≤ n) :
      MultipliesAt M n (C * ((n : ℝ) * Real.log n)) := by
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hden : 0 < (n : ℝ) * Real.log n :=
      mul_pos (by linarith) (Real.log_pos hnR)
    by_cases hn₀ : n₀ ≤ n
    · apply ClockedSupport.budget_mono (hbudget_large n hn₀ hn)
      exact mul_le_mul_of_nonneg_right (le_max_left A S) hden.le
    · apply ClockedSupport.budget_mono (hW n (by omega))
      apply (div_le_iff₀ hden).mp
      calc
        W n / ((n : ℝ) * Real.log n) ≤ D n := le_max_right _ _
        _ ≤ S := by
          change D n ≤ ∑ i ∈ Finset.range n₀, D i
          apply Finset.single_le_sum (f := D) (fun i _ => show 0 ≤ D i from le_max_left _ _)
          exact Finset.mem_range.mpr (by omega)
        _ ≤ C := le_max_right A S
  refine ⟨M, hcorrect, C, ?_⟩
  intro n b p T r hparams τ hτ
  have hd0 : 0 < d := by omega
  have hn : 2 ≤ n :=
    le_trans (Nat.succ_le_of_lt
      (Nat.one_lt_two_pow (by positivity) : 1 < 2 ^ (d ^ 12))) hparams.1
  apply ClockedSupport.budget_mono (huniform n hn)
  have hterm : 0 ≤ 12 * (T : ℝ) / r * τ :=
    mul_nonneg (by positivity) (ClockedSupport.budget_nonneg hτ)
  linarith

/-- Exact-type reduction. The imported Jain prerequisite is Open on Prove2Me. -/
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : IntMul.MultitapeTM,
      (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, IntMul.MultipliesAt M n τ) ∧
      ∃ C : ℝ, ∀ n b p T r : ℕ, IntMul.HvdH.StepParameters d n b p T r →
        ∀ τ : ℝ, IntMul.MultipliesAt M (3 * r * p) τ →
          IntMul.MultipliesAt M n
            (12 * (T : ℝ) / r * τ + C * ((n : ℝ) * Real.log n)) := by
  exact IntMul.HvdH.clocked_recursive_multiplier_of_kappa_bound
    (3666565558019 / 10 ^ 17) (by norm_num) IntMul.Kappa.jain_round6 d hd

