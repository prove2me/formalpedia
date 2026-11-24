-- Prove2me | solution 1 for GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T03:09:19.023774+00:00
-- url     : https://prove2.me/submissions/bfcb81f7-0249-47ec-af30-bd9f66c25c6b

import Mathlib


theorem solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) → ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  intro E _ _ n _ _ Y t ht ht1 hY m
  let Z : Matrix n n E := 1 + Y
  have prodB {A B : Matrix n n E} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (Ah : ∀ i j, ‖A i j‖ ≤ a) (Bh : ∀ i j, ‖B i j‖ ≤ b) (i j : n) : ‖(A*B) i j‖ ≤ a*b := by
    rw [Matrix.mul_apply]; apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb)
    intro k _; rw [norm_mul]; exact mul_le_mul (Ah i k) (Bh k j) (norm_nonneg _) ha
  have hz (i j : n) : ‖Z i j‖ ≤ 1 := by
    apply (IsUltrametricDist.norm_add_le_max _ _).trans; apply max_le _ ((hY _ _).trans ht1)
    by_cases e : i=j <;> simp [Matrix.one_apply,e]
  have lin (k : ℕ) (i j : n) : ‖(Z^k-1) i j‖ ≤ t := by
    induction k generalizing i j with
    | zero => simpa using ht
    | succ k ih =>
      have eq : Z^(k+1)-1 = (Z^k-1)*Z + Y := by rw [pow_succ,sub_mul,one_mul]; dsimp [Z]; abel
      rw [eq]; apply (IsUltrametricDist.norm_add_le_max _ _).trans; apply max_le _ (hY _ _)
      simpa using prodB ht zero_le_one ih hz i j
  change ∀ i j, ‖(Z^m-1-(m:E) • Y) i j‖ ≤ t^2
  induction m with
  | zero => simp [sq_nonneg]
  | succ m ih =>
    have eq : Z^(m+1)-1-((m+1:ℕ):E) • Y = (Z^m-1-(m:E) • Y) + (Z^m-1)*Y := by
      rw [pow_succ,show Z=1+Y from rfl,mul_add,mul_one,sub_mul,one_mul]; push_cast; rw [add_smul,one_smul]; abel
    intro i j; rw [eq]; apply (IsUltrametricDist.norm_add_le_max _ _).trans
    exact max_le (ih _ _) (by simpa [pow_two] using prodB ht ht (lin m) hY i j)
