-- Prove2me | solution 1 for MultiSecretary.BR.online_le_offline
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:37:12.63748+00:00
-- url     : https://prove2.me/submissions/6ac077ee-2556-4be6-9e59-ecc854b95b6c

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model

open MultiSecretary.BR Finset in
theorem MultiSecretary.BR.feasible_of_mem_policies_a21 {m n k : ℕ}
    (σ : (Fin n → Fin m) → Fin n → Bool) (hσ : σ ∈ policies n m k) : IsFeasible k σ := by
  classical
  unfold policies at hσ
  rw [Finset.mem_filter] at hσ
  exact hσ.2.2

open MultiSecretary.BR Finset in
theorem solution {m : ℕ} (I : Instance m) (n k : ℕ) (hk : k ≤ n)
    (σ : (Fin n → Fin m) → Fin n → Bool) (hσ : σ ∈ policies n m k) :
    I.value σ ≤ I.Voff n k := by
  classical
  have hf := MultiSecretary.BR.feasible_of_mem_policies_a21 σ hσ
  unfold Instance.value Instance.Voff Instance.E
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left
  · exact Finset.le_sup'_of_le _ (b := σ x) (by simpa using hf x) le_rfl
  · unfold Instance.weight
    exact Finset.prod_nonneg (fun t _ => (I.f_pos _).le)
