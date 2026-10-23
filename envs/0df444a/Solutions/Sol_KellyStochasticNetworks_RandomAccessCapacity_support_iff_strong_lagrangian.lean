-- Prove2me | solution 1 for KellyStochasticNetworks.RandomAccessCapacity.support_iff_strong_lagrangian
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:04:27.601458+00:00
-- url     : https://prove2.me/submissions/5ac18aab-df69-413b-9d08-c1346f6e201a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Optimization

theorem solution : ¬ (∀ {n m : ℕ} (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → Fin m → ℝ)
    (b : Fin m → ℝ),
    let φ : (Fin m → ℝ) → EReal := fun c =>
      sInf {v : EReal | ∃ x ∈ X, h x = c ∧ v = (f x : EReal)}
    (∃ a : ℝ, ∃ y : Fin m → ℝ, φ b = (a : EReal) ∧
      ∀ c, ((a + ∑ i, y i * (c i - b i) : ℝ) : EReal) ≤ φ c) ↔
    ∃ y : Fin m → ℝ, φ b =
      sInf {v : EReal | ∃ x ∈ X,
        v = ((f x + ∑ i, y i * (b i - h x i) : ℝ) : EReal)}) := by
  intro H
  have := H (n := 1) (m := 1) (∅ : Set (Fin 1 → ℝ)) (fun _ => 0) (fun _ => 0) 0
  simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.ofPred_false, sInf_empty] at this
  have h2 := this.mpr ⟨0, trivial⟩
  obtain ⟨a, -, ha, -⟩ := h2
  exact EReal.coe_ne_top a ha.symm
