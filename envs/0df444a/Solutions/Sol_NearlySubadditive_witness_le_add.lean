-- Prove2me | solution 1 for NearlySubadditive.witness_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:35.843943+00:00
-- url     : https://prove2.me/submissions/caa05dc2-1957-4941-b6e1-76240ca2ae43

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
section
@[expose] public section
noncomputable section
open Filter Finset
open scoped Topology
namespace NearlySubadditive
variable {f : ℕ → ℝ}
private theorem sum_block_le (hf0 : 0 ≤ f) (hf : Monotone f) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ∑ k ∈ range n, f (m + 1 + k) / ((m + 1 + k : ℕ) : ℝ) ^ 2 ≤
      f (m + n) * (1 / m - 1 / (m + n : ℕ)) := by
  have := sum_Ioc_inv_sq_le_sub (α := ℝ) hm.ne' (Nat.le_add_right m n)
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show m + n + 1 - (m + 1) = n by omega] at this
  rw [one_div, one_div]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left this (hf0 _))
  rw [mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hf (by have := mem_range.1 hk; omega)) (sq_nonneg _)
end NearlySubadditive
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hf0 : 0 ≤ f) (hf : Monotone f) (m n : ℕ) :
    witness f (m + n) ≤ witness f m + witness f n + f (m + n) := by
  set A : ℕ → ℝ := fun p ↦ ∑ i ∈ range (p + 1), f i / (i : ℝ) ^ 2
  have hA : ∀ p q, A (p + q) = A p + ∑ k ∈ range q, f (p + 1 + k) / ((p + 1 + k : ℕ) : ℝ) ^ 2 :=
    fun p q ↦ by
      change ∑ i ∈ range (p + q + 1), _ = _
      rw [show p + q + 1 = p + 1 + q by omega]
      exact sum_range_add _ _ _
  have hw : ∀ p, witness f p = p * A p := fun _ ↦ rfl
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa [hw] using hf0 n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [hw] using hf0 m
  have h1 := sum_block_le hf0 hf hm n
  have h2 := sum_block_le hf0 hf hn m
  rw [add_comm n m] at h2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 := hA m n
  have e2 := hA n m
  rw [add_comm n m] at e2
  rw [hw, hw, hw]
  push_cast at h1 h2 e1 e2 ⊢
  have key : (m : ℝ) * (f (m + n) * (1 / m - 1 / (m + n))) +
      n * (f (m + n) * (1 / n - 1 / (m + n))) = f (m + n) := by
    field_simp; ring
  have b1 := mul_le_mul_of_nonneg_left h1 hmR.le
  have b2 := mul_le_mul_of_nonneg_left h2 hnR.le
  have p1 := congrArg (fun t ↦ (m : ℝ) * t) e1
  have p2 := congrArg (fun t ↦ (n : ℝ) * t) e2
  simp only [mul_add] at p1 p2
  rw [add_mul]
  linarith
end NearlySubadditive
