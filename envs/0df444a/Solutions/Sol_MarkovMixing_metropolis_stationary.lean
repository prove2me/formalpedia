-- Prove2me | solution 1 for MarkovMixing.metropolis_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:51:42.3681+00:00
-- url     : https://prove2.me/submissions/f95bbde6-10b5-4246-8293-2cf58c7a6683

import Definitions.Def_mm_mcmc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (hΨ : IsStochastic Ψ) (hsymm : ∀ x y : V, Ψ x y = Ψ y x)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x) :
    IsStochastic (metropolis Ψ π) ∧
    DetailedBalance (metropolis Ψ π) π ∧
    IsStationary (metropolis Ψ π) π := by
  classical
  -- the basic acceptance identity `a · min(1, b/a) = min(a,b)`
  have hminmul : ∀ a b : ℝ, 0 < a → a * min 1 (b / a) = min a b := by
    intro a b ha
    rcases le_total b a with h | h
    · rw [min_eq_right (by rw [div_le_one ha]; exact h), min_eq_right h]
      field_simp
    · rw [min_eq_left (by rw [le_div_iff₀ ha]; linarith), min_eq_left h, mul_one]
  have hoff : ∀ x y : V, y ≠ x → metropolis Ψ π x y = Ψ x y * min 1 (π y / π x) := by
    intro x y hxy
    show (if y = x then _ else _) = _
    rw [if_neg hxy]
  have hdiag : ∀ x : V, metropolis Ψ π x x
      = 1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z / π x) := by
    intro x
    show (if x = x then _ else _) = _
    rw [if_pos rfl]
  -- row sums
  have hrow : ∀ x : V, ∑ y, metropolis Ψ π x y = 1 := by
    intro x
    have hsp : ∑ y ∈ ({x}ᶜ : Finset V), metropolis Ψ π x y
        + ∑ y ∈ ({x} : Finset V), metropolis Ψ π x y = ∑ y, metropolis Ψ π x y :=
      Finset.sum_compl_add_sum _ _
    rw [← hsp, Finset.sum_singleton, hdiag x]
    have hcongr : ∑ y ∈ ({x}ᶜ : Finset V), metropolis Ψ π x y
        = ∑ y ∈ ({x}ᶜ : Finset V), Ψ x y * min 1 (π y / π x) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [hoff x y (by simpa using Finset.mem_compl.mp hy)]
    rw [hcongr]
    ring
  -- nonnegativity
  have hacc_nonneg : ∀ x y : V, 0 ≤ min 1 (π y / π x) :=
    fun x y => le_min zero_le_one (div_nonneg (hpos y).le (hpos x).le)
  have hacc_le : ∀ x y : V, min 1 (π y / π x) ≤ 1 := fun x y => min_le_left _ _
  have hnonneg : ∀ x y : V, 0 ≤ metropolis Ψ π x y := by
    intro x y
    by_cases hxy : y = x
    · subst hxy
      rw [hdiag y]
      have hle : ∑ z ∈ ({y}ᶜ : Finset V), Ψ y z * min 1 (π z / π y)
          ≤ ∑ z ∈ ({y}ᶜ : Finset V), Ψ y z := by
        refine Finset.sum_le_sum fun z _ => ?_
        calc Ψ y z * min 1 (π z / π y) ≤ Ψ y z * 1 :=
              mul_le_mul_of_nonneg_left (hacc_le y z) (hΨ.1 y z)
          _ = Ψ y z := mul_one _
      have hsum : ∑ z ∈ ({y}ᶜ : Finset V), Ψ y z + Ψ y y = 1 := by
        have := Finset.sum_compl_add_sum ({y} : Finset V) (fun z => Ψ y z)
        rw [Finset.sum_singleton] at this
        rw [this]
        exact hΨ.2 y
      have := hΨ.1 y y
      linarith
    · rw [hoff x y hxy]
      exact mul_nonneg (hΨ.1 x y) (hacc_nonneg x y)
  have hstoch : IsStochastic (metropolis Ψ π) := ⟨hnonneg, hrow⟩
  -- detailed balance
  have hdb : DetailedBalance (metropolis Ψ π) π := by
    intro x y
    by_cases hxy : y = x
    · subst hxy; rfl
    · have hyx : x ≠ y := fun h => hxy h.symm
      rw [hoff x y hxy, hoff y x hyx]
      have h1 : π x * (Ψ x y * min 1 (π y / π x)) = Ψ x y * min (π x) (π y) := by
        rw [← hminmul (π x) (π y) (hpos x)]; ring
      have h2 : π y * (Ψ y x * min 1 (π x / π y)) = Ψ y x * min (π y) (π x) := by
        rw [← hminmul (π y) (π x) (hpos y)]; ring
      rw [h1, h2, hsymm x y, min_comm (π y) (π x)]
  refine ⟨hstoch, hdb, hπ, ?_⟩
  funext y
  show ∑ x, π x * metropolis Ψ π x y = π y
  rw [Finset.sum_congr rfl fun x _ => (hdb y x).symm, ← Finset.mul_sum, hrow y, mul_one]
