-- Prove2me | solution 1 for NisanRonen.Rounding.dominant_actual_le_of_allocation_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:42:26.060508+00:00
-- url     : https://prove2.me/submissions/efd9f4ac-0902-4127-8253-ec4e32c30a8f

import Theorems.Thm_NisanRonen_Rounding_dominant_iff_rounded_optimal
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound

open NisanRonen.Rounding

theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (s : Fin n → Strategy n k) (hs : ∀ i, IsDominant f δ a b i (t i) (s i))
    (C : ℝ)
    (hC : ∀ i : Fin n, ∃ d : Fin n → Fin k → ℝ,
      (∀ l j, a ≤ d l j ∧ d l j ≤ b) ∧ d i = (s i).decl ∧
      allocOf f δ d = allocOf f δ (fun l => (s l).decl) ∧
      ∃ y : Fin k → Fin n,
        roundedMakespan δ y (corrStar y (Function.update d i (t i))) ≤ C) :
    makespan (allocOf f δ (fun l => (s l).decl)) (actualTimes f δ s) ≤ C := by
  classical
  unfold makespan
  apply Finset.sup'_le
  intro i _
  obtain ⟨d, hd, hdi, hx, y, hy⟩ := hC i
  let q : Fin n → Strategy n k := fun l => ⟨d l, fun _ => d l⟩
  have hup : (fun l => (Function.update q i (s i) l).decl) = d := by
    funext l
    by_cases he : l = i
    · subst l
      simpa only [Function.update_self] using hdi.symm
    · simp [Function.update_of_ne he, q]
  have hdom := ((dominant_iff_rounded_optimal ha hab hδ f hf t ht i (s i) (hs i).1).mp
    (hs i)) q (fun l _ j => hd l j) y
  rw [hup] at hdom
  let x := allocOf f δ d
  let τ := corr i x d ((s i).exec x)
  have hτ : ∀ j, a ≤ τ j := by
    intro j
    by_cases hj : x j = i
    · simpa [τ, corr, hj] using (ht i j).1.trans ((hs i).1.2 x j hj)
    · simpa [τ, corr, hj] using (hd (x j) j).1
  have hload : load x (actualTimes f δ s) i = load x τ i := by
    unfold load
    apply Finset.sum_congr rfl
    intro j hj
    have he : x j = i := (Finset.mem_filter.mp hj).2
    simp [τ, x, corr, actualTimes, ← hx, he]
  rw [← hx, hload]
  exact (Finset.le_sup' _ (Finset.mem_univ i)).trans
    ((rounding_error_bound ha hδ x τ hτ).1.trans (hdom.trans hy))
