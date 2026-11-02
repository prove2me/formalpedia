-- Prove2me | solution 1 for MLRPCake.EnvyFree.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:48:27.379985+00:00
-- url     : https://prove2.me/submissions/a5dd379f-f99a-4c69-9d94-8d52b04bcef6

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Theorems.Thm_MLRPCake_EnvyFree_lemma_4
import Theorems.Thm_MLRPCake_EnvyFree_coalesce_envy_free

open MLRPCake.EnvyFree

theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < η → η < 1 →
    ∃ T : ℕ, bsStops f (η / lam) T ∧ (∀ k < T, ¬ bsStops f (η / lam) k) ∧
      (T : ℝ) ≤ c * ((n : ℝ) + Real.logb 2 lam + Real.logb 2 (1 / η) + 1) ^ c ∧
      IsAllocation (n := n) (coalesce n (bsOutput f (η / lam) T)) ∧
      EnvyFreeUpTo f η (coalesce n (bsOutput f (η / lam) T)) := by
  obtain ⟨c, hc⟩ := MLRPCake.EnvyFree.lemma_4
  refine ⟨c * 2 ^ c, ?_⟩
  intro n f lam η hn hf hmlrp hlam hL hη0 hη1
  have hlam0 : 0 < lam := by linarith
  have hδ0 : 0 < η / lam := div_pos hη0 hlam0
  have hδ1 : η / lam < 1 := by
    rw [div_lt_one hlam0]; linarith
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hc n f lam (η / lam) hn hf hlam hL hδ0 hδ1
  obtain ⟨hA, hE⟩ := MLRPCake.EnvyFree.coalesce_envy_free n f lam η _ hn hf hmlrp hlam hL hη0 hT4
  refine ⟨T, hT1, hT2, ?_, hA, hE⟩
  -- bound
  set L := Real.logb 2 lam with hLdef
  set E := Real.logb 2 (1 / η) with hEdef
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hlam
  have hE0 : 0 ≤ E := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hη0]; linarith)
  have hsplit : Real.logb 2 (1 / (η / lam)) = L + E := by
    rw [hLdef, hEdef, ← Real.logb_mul (by positivity) (by positivity)]
    congr 1; field_simp
  rw [hsplit] at hT3
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  set S : ℝ := (n : ℝ) + L + E + 1 with hS
  have hS1 : 1 ≤ S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have h2 : (n : ℝ) + L + (L + E) + 1 ≤ 2 * S := by linarith
  have hpow : ((n : ℝ) + L + (L + E) + 1) ^ c ≤ (2 * S) ^ c :=
    pow_le_pow_left₀ (by linarith) h2 c
  have hc2 : c ≤ c * 2 ^ c := Nat.le_mul_of_pos_right c (by positivity)
  have hSpow : S ^ c ≤ S ^ (c * 2 ^ c) := pow_le_pow_right₀ hS1 hc2
  calc (T : ℝ) ≤ c * ((n : ℝ) + L + (L + E) + 1) ^ c := hT3
    _ ≤ c * (2 * S) ^ c := by gcongr
    _ = (c * 2 ^ c : ℕ) * S ^ c := by push_cast; rw [mul_pow]; ring
    _ ≤ (c * 2 ^ c : ℕ) * S ^ (c * 2 ^ c) := by gcongr
