-- Prove2me | solution 1 for NQueensComp.NPC.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:36:41.906155+00:00
-- url     : https://prove2.me/submissions/aa7d71ff-7024-4b05-8187-09b487cdf657

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

open NQueensComp.NPC

/-- Two numbers below `n` plus distinct multiples of `n` differ. -/
theorem key_col (n x y u v : ℕ) (hx : x < n) (hy : y < n) (huv : u ≠ v) :
    x + n * u ≠ y + n * v := by
  intro heq
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have : n * (u + 1) ≤ n * v := Nat.mul_le_mul_left n h
    nlinarith
  · have : n * (v + 1) ≤ n * u := Nat.mul_le_mul_left n h
    nlinarith

/-- Two integers `x, y` with `|x - y| < 2n` plus multiples of `n` whose factors differ by more
than `1` are different. -/
theorem key_diag (n : ℕ) (x y u v : ℤ) (hxy : |x - y| < 2 * (n : ℤ)) (huv : 1 < |u - v|) :
    x + n * u ≠ y + n * v := by
  intro heq
  have h1 : x - y = (n : ℤ) * (v - u) := by linarith
  have h2 : |x - y| = (n : ℤ) * |v - u| := by
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ n)]
  rw [abs_sub_comm] at huv
  have : (n : ℤ) * 2 ≤ (n : ℤ) * |v - u| := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    omega
  linarith

theorem solution (n : ℕ) (q₁ q₂ q₃ q₄ : Queen) (h₁ : FitsOn n q₁) (h₂ : FitsOn n q₂) :
    (col q₃ ≠ col q₄ → col (q₁ + n • q₃) ≠ col (q₂ + n • q₄)) ∧
    (row q₃ ≠ row q₄ → row (q₁ + n • q₃) ≠ row (q₂ + n • q₄)) ∧
    (1 < |((sumDiag q₃ : ℕ) : ℤ) - ((sumDiag q₄ : ℕ) : ℤ)| →
      sumDiag (q₁ + n • q₃) ≠ sumDiag (q₂ + n • q₄)) ∧
    (1 < |diffDiag q₃ - diffDiag q₄| → diffDiag (q₁ + n • q₃) ≠ diffDiag (q₂ + n • q₄)) ∧
    (col q₃ ≠ col q₄ → row q₃ ≠ row q₄ →
      1 < |((sumDiag q₃ : ℕ) : ℤ) - ((sumDiag q₄ : ℕ) : ℤ)| →
      1 < |diffDiag q₃ - diffDiag q₄| → ¬ Attacks (q₁ + n • q₃) (q₂ + n • q₄)) := by
  obtain ⟨a₁, b₁⟩ := q₁
  obtain ⟨a₂, b₂⟩ := q₂
  obtain ⟨a₃, b₃⟩ := q₃
  obtain ⟨a₄, b₄⟩ := q₄
  simp only [FitsOn, size, max_lt_iff] at h₁ h₂
  obtain ⟨ha₁, hb₁⟩ := h₁
  obtain ⟨ha₂, hb₂⟩ := h₂
  simp only [col, row, sumDiag, diffDiag, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  have hc : a₃ ≠ a₄ → a₁ + n * a₃ ≠ a₂ + n * a₄ := fun h => key_col n _ _ _ _ ha₁ ha₂ h
  have hr : b₃ ≠ b₄ → b₁ + n * b₃ ≠ b₂ + n * b₄ := fun h => key_col n _ _ _ _ hb₁ hb₂ h
  have hs : 1 < |((a₃ + b₃ : ℕ) : ℤ) - ((a₄ + b₄ : ℕ) : ℤ)| →
      a₁ + n * a₃ + (b₁ + n * b₃) ≠ a₂ + n * a₄ + (b₂ + n * b₄) := by
    intro h heq
    have := key_diag n ((a₁ : ℤ) + b₁) ((a₂ : ℤ) + b₂) ((a₃ : ℤ) + b₃) ((a₄ : ℤ) + b₄)
      (by rw [abs_lt]; constructor <;> push_cast <;> omega) (by push_cast at h ⊢; exact h)
    apply this
    push_cast
    have := congrArg (fun x : ℕ => (x : ℤ)) heq
    push_cast at this
    linarith
  have hd : 1 < |((a₃ : ℤ) - b₃) - ((a₄ : ℤ) - b₄)| →
      ((a₁ + n * a₃ : ℕ) : ℤ) - ((b₁ + n * b₃ : ℕ) : ℤ) ≠
        ((a₂ + n * a₄ : ℕ) : ℤ) - ((b₂ + n * b₄ : ℕ) : ℤ) := by
    intro h heq
    have := key_diag n ((a₁ : ℤ) - b₁) ((a₂ : ℤ) - b₂) ((a₃ : ℤ) - b₃) ((a₄ : ℤ) - b₄)
      (by rw [abs_lt]; constructor <;> omega) h
    apply this
    push_cast at heq
    linarith
  refine ⟨hc, hr, hs, hd, ?_⟩
  intro h3 h4 h5 h6
  simp only [Attacks, col, row, sumDiag, diffDiag, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, not_and, not_or]
  intro _
  exact ⟨hc h3, hr h4, hs h5, hd h6⟩
