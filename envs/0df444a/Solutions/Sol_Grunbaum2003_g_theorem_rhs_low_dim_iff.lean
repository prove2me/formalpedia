-- Prove2me | solution 1 for Grunbaum2003.g_theorem_rhs_low_dim_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:15:56.322368+00:00
-- url     : https://prove2.me/submissions/bb9a4100-c845-43d7-82dc-8f97baf762e8

import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003


/-- The first positive Macaulay condition permits every natural first entry. -/
theorem isMSequence_one_iff (g : ℕ → ℕ) : IsMSequence 1 g ↔ g 0 = 1 := by
  constructor
  · exact fun h => h.1
  · intro hg₀
    refine ⟨hg₀, ?_⟩
    intro k hk₀ hk₁
    have hk : k = 1 := by omega
    subst k
    by_cases hz : g 1 = 0
    · exact Or.inl hz
    · refine Or.inr ⟨1, fun _ => g 1, by omega, le_refl _, ?_, ?_, ?_, ?_⟩
      · change 1 ≤ g 1
        omega
      · intro r s hr hrs hs
        omega
      · simp only [Finset.Icc_self, Finset.sum_singleton, Nat.choose_one_right]
      · simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
          Nat.choose_zero_right, hg₀, le_refl]

/-- In dimension one, the arithmetic side of the exact g-theorem prescribes two vertices. -/
theorem g_theorem_rhs_dim_one_iff (f : Fin 2 → ℤ) :
    (∃ g : ℕ → ℕ, IsMSequence (1 / 2) g ∧
      ∀ k : Fin 2, f k = ∑ j ∈ Finset.range (1 / 2 + 1),
        (g j : ℤ) * gTheoremMatrix 1 j k.val) ↔
      f 0 = 1 ∧ f 1 = 2 := by
  constructor
  · rintro ⟨g, hg, hf⟩
    have h₀ := hf 0
    have h₁ := hf 1
    norm_num [gTheoremMatrix, hg.1] at h₀ h₁
    exact ⟨h₀, h₁⟩
  · rintro ⟨h₀, h₁⟩
    refine ⟨fun _ => 1, ⟨rfl, ?_⟩, ?_⟩
    · intro k hk₀ hk₁
      omega
    · intro k
      fin_cases k <;> norm_num [gTheoremMatrix, h₀, h₁]

/-- Dimension two reduces to the face vector of a polygon with n+3 vertices. -/
theorem g_theorem_rhs_dim_two_iff (f : Fin 3 → ℤ) :
    (∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
      ∀ k : Fin 3, f k = ∑ j ∈ Finset.range (2 / 2 + 1),
        (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
      f 0 = 1 ∧ ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3 := by
  constructor
  · rintro ⟨g, hg, hf⟩
    have h₀ := hf 0
    have h₁ := hf 1
    have h₂ := hf 2
    norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, hg.1] at h₀ h₁ h₂
    refine ⟨h₀, g 1, ?_, ?_⟩ <;> omega
  · rintro ⟨h₀, n, h₁, h₂⟩
    let g : ℕ → ℕ := fun i => if i = 0 then 1 else n
    refine ⟨g, (isMSequence_one_iff g).mpr (by simp only [g, if_pos rfl]), ?_⟩
    intro k
    fin_cases k
    · change f 0 = _
      rw [h₀]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
    · change f 1 = _
      rw [h₁]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega
    · change f 2 = _
      rw [h₂]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega

/-- Dimension three prescribes exactly the simplicial three-polytope face equations. -/
theorem g_theorem_rhs_dim_three_iff (f : Fin 4 → ℤ) :
    (∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
      ∀ k : Fin 4, f k = ∑ j ∈ Finset.range (3 / 2 + 1),
        (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
      f 0 = 1 ∧ ∃ n : ℕ,
        f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4 := by
  constructor
  · rintro ⟨g, hg, hf⟩
    have h₀ := hf 0
    have h₁ := hf 1
    have h₂ := hf 2
    have h₃ := hf 3
    norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, hg.1] at h₀ h₁ h₂ h₃
    refine ⟨h₀, g 1, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨h₀, n, h₁, h₂, h₃⟩
    let g : ℕ → ℕ := fun i => if i = 0 then 1 else n
    refine ⟨g, (isMSequence_one_iff g).mpr (by simp only [g, if_pos rfl]), ?_⟩
    intro k
    fin_cases k
    · change f 0 = _
      rw [h₀]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
    · change f 1 = _
      rw [h₁]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega
    · change f 2 = _
      rw [h₂]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega
    · change f 3 = _
      rw [h₃]
      norm_num [gTheoremMatrix, Nat.choose, Finset.sum_range_succ, g]
      omega


theorem g_theorem_rhs_low_dim_iff :
    (∀ g : ℕ → ℕ, IsMSequence 1 g ↔ g 0 = 1) ∧
    (∀ f : Fin 2 → ℤ,
      (∃ g : ℕ → ℕ, IsMSequence (1 / 2) g ∧
        ∀ k : Fin 2, f k = ∑ j ∈ Finset.range (1 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 1 j k.val) ↔
        f 0 = 1 ∧ f 1 = 2) ∧
    (∀ f : Fin 3 → ℤ,
      (∃ g : ℕ → ℕ, IsMSequence (2 / 2) g ∧
        ∀ k : Fin 3, f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 2 j k.val) ↔
        f 0 = 1 ∧ ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3) ∧
    (∀ f : Fin 4 → ℤ,
      (∃ g : ℕ → ℕ, IsMSequence (3 / 2) g ∧
        ∀ k : Fin 4, f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * gTheoremMatrix 3 j k.val) ↔
        f 0 = 1 ∧ ∃ n : ℕ,
          f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4) :=
  ⟨isMSequence_one_iff, g_theorem_rhs_dim_one_iff, g_theorem_rhs_dim_two_iff, g_theorem_rhs_dim_three_iff⟩

end Grunbaum2003

theorem solution :
    (∀ g : ℕ → ℕ, Grunbaum2003.IsMSequence 1 g ↔ g 0 = 1) ∧
    (∀ f : Fin 2 → ℤ,
      (∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (1 / 2) g ∧
        ∀ k : Fin 2, f k = ∑ j ∈ Finset.range (1 / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix 1 j k.val) ↔
        f 0 = 1 ∧ f 1 = 2) ∧
    (∀ f : Fin 3 → ℤ,
      (∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (2 / 2) g ∧
        ∀ k : Fin 3, f k = ∑ j ∈ Finset.range (2 / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix 2 j k.val) ↔
        f 0 = 1 ∧ ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3) ∧
    (∀ f : Fin 4 → ℤ,
      (∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (3 / 2) g ∧
        ∀ k : Fin 4, f k = ∑ j ∈ Finset.range (3 / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix 3 j k.val) ↔
        f 0 = 1 ∧ ∃ n : ℕ,
          f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4) :=
  Grunbaum2003.g_theorem_rhs_low_dim_iff
