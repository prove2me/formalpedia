-- Prove2me | solution 1 for ModernConvex.SLemma.inhomogeneous_s_lemma
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:50:52.311018+00:00
-- url     : https://prove2.me/submissions/f072c6b0-349a-4267-aff3-9995ff31816d

import Mathlib
open Matrix

theorem solution : ¬ (∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (a b : Fin n → ℝ) (α β : ℝ)
    (hf : ∃ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α < 0),
    ((∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α ≤ 0 →
        x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ 0) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ ∀ x : Fin n → ℝ,
        x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ lam * (x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α)) ∧
    ((∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α ≤ 0 →
        x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ 0) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => lam * α)
          (Matrix.of fun (_ : Unit) (j : Fin n) => (lam • a - b) j)
          (Matrix.of fun (i : Fin n) (_ : Unit) => (lam • a - b) i) (lam • A - B)).PosSemidef) ∧
    ((∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β) →
      (∀ lam : ℝ, 0 ≤ lam → (∀ x : Fin n → ℝ,
          x ⬝ᵥ (B *ᵥ x) + 2 * (b ⬝ᵥ x) + β ≤ lam * (x ⬝ᵥ (A *ᵥ x) + 2 * (a ⬝ᵥ x) + α)) →
        0 < lam) ∧
      (∀ lam : ℝ, 0 ≤ lam →
        (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => lam * α)
          (Matrix.of fun (_ : Unit) (j : Fin n) => (lam • a - b) j)
          (Matrix.of fun (i : Fin n) (_ : Unit) => (lam • a - b) i) (lam • A - B)).PosSemidef →
        0 < lam))) := by
  intro h
  have h2 := (h (n := 0) 0 0 (by simp) (by simp) 0 0 (-1) 1 ⟨0, by simp⟩).2.1
  have hR : ∃ lam : ℝ, 0 ≤ lam ∧
        (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => lam * (-1 : ℝ))
          (Matrix.of fun (_ : Unit) (j : Fin 0) => (lam • (0 : Fin 0 → ℝ) - 0) j)
          (Matrix.of fun (i : Fin 0) (_ : Unit) => (lam • (0 : Fin 0 → ℝ) - 0) i)
          (lam • (0 : Matrix (Fin 0) (Fin 0) ℝ) - 0)).PosSemidef := by
    refine ⟨0, le_rfl, ?_⟩
    have : (Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => (0 : ℝ) * (-1 : ℝ))
          (Matrix.of fun (_ : Unit) (j : Fin 0) => ((0 : ℝ) • (0 : Fin 0 → ℝ) - 0) j)
          (Matrix.of fun (i : Fin 0) (_ : Unit) => ((0 : ℝ) • (0 : Fin 0 → ℝ) - 0) i)
          ((0 : ℝ) • (0 : Matrix (Fin 0) (Fin 0) ℝ) - 0)) = 0 := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · simp
      · exact j.elim0
      · exact i.elim0
      · exact i.elim0
    rw [this]; exact PosSemidef.zero
  have := h2.2 hR 0 (by simp)
  norm_num at this
