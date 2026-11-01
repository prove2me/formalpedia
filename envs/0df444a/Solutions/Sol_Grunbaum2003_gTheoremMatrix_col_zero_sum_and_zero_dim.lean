-- Prove2me | solution 1 for Grunbaum2003.gTheoremMatrix_col_zero_sum_and_zero_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:22.930833+00:00
-- url     : https://prove2.me/submissions/876168b8-ce88-464f-9b50-2265b01f6c32

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem gTheoremMatrix_zero_right (d j : ℕ) (hj : j ≤ d / 2) :
    gTheoremMatrix d j 0 = if j = 0 then 1 else 0 := by
  unfold gTheoremMatrix
  split_ifs with h0
  · subst h0
    simp [Nat.choose_self]
  · have h1 : d + 1 - j < d + 1 := by omega
    have h2 : j < d + 1 := by omega
    simp only [tsub_zero]
    rw [Nat.choose_eq_zero_of_lt h1, Nat.choose_eq_zero_of_lt h2]
    simp

/-- Grünbaum (2003), §10.6 (pp. 198a–198b): column 0 of Björner's matrix `M_d` selects
`g 0`, and the `g`-theorem equivalence holds unconditionally in dimension `d = 0`. -/
theorem gTheoremMatrix_col_zero_sum_and_zero_dim :
    (∀ (d : ℕ) (g : ℕ → ℕ),
      ∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0 = (g 0 : ℤ)) ∧
    (∀ f : Fin 1 → ℤ,
      (f 0 = 1 ∧ ∃ P : Set (Fin 0 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 0, f j.succ = (faceCount P j.val : ℤ)) ↔
      ∃ g : ℕ → ℕ, IsMSequence 0 g ∧
        ∀ k : Fin 1,
          f k = ∑ j ∈ Finset.range 1,
            (g j : ℤ) * gTheoremMatrix 0 j k.val) := by
  refine ⟨?_, ?_⟩
  · intro d g
    rw [Finset.sum_range_succ']
    have htail : ∑ x ∈ Finset.range (d / 2), (g (x + 1) : ℤ) * gTheoremMatrix d (x + 1) 0 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro x hx
      rw [Finset.mem_range] at hx
      rw [gTheoremMatrix_zero_right d (x + 1) (by omega)]
      simp
    rw [htail, zero_add, gTheoremMatrix_zero_right d 0 (Nat.zero_le _)]
    simp
  · intro f
    have hSimp0 : IsSimplicialDPolytope ({0} : Set (Fin 0 → ℝ)) := by
      refine ⟨⟨⟨{0}, Set.finite_singleton 0, Set.singleton_nonempty 0,
        (convexHull_singleton (0 : Fin 0 → ℝ)).symm⟩, ?_⟩, ?_⟩
      · rw [eq_top_iff]
        intro x _
        have hx : x = 0 := Subsingleton.elim x 0
        subst hx
        exact subset_affineSpan ℝ _ (Set.mem_singleton 0)
      · intro F _ _ hdim
        omega
    constructor
    · rintro ⟨hf0, _⟩
      refine ⟨fun _ => 1, ⟨rfl, fun k hk1 hk2 => by omega⟩, ?_⟩
      intro k
      have hk0 : k = 0 := Subsingleton.elim k 0
      subst hk0
      simp [gTheoremMatrix, hf0]
    · rintro ⟨g, hg, hfk⟩
      refine ⟨?_, {0}, hSimp0, fun j => Fin.elim0 j⟩
      have h0 := hfk 0
      simpa [gTheoremMatrix, hg.1] using h0

end Grunbaum2003

theorem solution :
    (∀ (d : ℕ) (g : ℕ → ℕ),
      ∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * Grunbaum2003.gTheoremMatrix d j 0 = (g 0 : ℤ)) ∧
    (∀ f : Fin 1 → ℤ,
      (f 0 = 1 ∧ ∃ P : Set (Fin 0 → ℝ),
        Grunbaum2003.IsSimplicialDPolytope P ∧
        ∀ j : Fin 0, f j.succ = (Grunbaum2003.faceCount P j.val : ℤ)) ↔
      ∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence 0 g ∧
        ∀ k : Fin 1,
          f k = ∑ j ∈ Finset.range 1,
            (g j : ℤ) * Grunbaum2003.gTheoremMatrix 0 j k.val) :=
  Grunbaum2003.gTheoremMatrix_col_zero_sum_and_zero_dim
