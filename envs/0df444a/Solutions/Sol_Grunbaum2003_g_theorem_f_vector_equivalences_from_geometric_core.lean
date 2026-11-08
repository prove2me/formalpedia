-- Prove2me | solution 1 for Grunbaum2003.g_theorem_f_vector_equivalences_from_geometric_core
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T03:46:04.469521+00:00
-- url     : https://prove2.me/submissions/b3faf270-190f-42b3-897f-5c66f5d5ed21

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators Classical

noncomputable section

namespace Grunbaum2003

theorem gTheoremMatrix_col_zero (d j : ℕ) (hj : j ≤ d) :
    gTheoremMatrix d j 0 = if j = 0 then 1 else 0 := by
  unfold gTheoremMatrix
  by_cases hj0 : j = 0
  · subst hj0
    simp
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have h1 : d + 1 - j < d + 1 := Nat.sub_lt (Nat.succ_pos d) hjpos
    have h2 : j < d + 1 := Nat.lt_succ_of_le hj
    have hc1 : Nat.choose (d + 1 - j) (d + 1) = 0 := Nat.choose_eq_zero_of_lt h1
    have hc2 : Nat.choose j (d + 1) = 0 := Nat.choose_eq_zero_of_lt h2
    simp [hj0, hc1, hc2]

theorem gTheoremMatrix_sum_col_zero (d : ℕ) (g : ℕ → ℕ) (hg0 : g 0 = 1) :
    (∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0) = 1 := by
  have hcongr :
      ∀ j ∈ Finset.range (d / 2 + 1),
        (g j : ℤ) * gTheoremMatrix d j 0 = if j = 0 then (g 0 : ℤ) else 0 := by
    intro j hj
    have hjle : j ≤ d := by
      have : j < d / 2 + 1 := Finset.mem_range.mp hj
      omega
    rw [gTheoremMatrix_col_zero d j hjle]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl hcongr]
  simp [hg0]

end Grunbaum2003

namespace Grunbaum2003

/-- Reduction of the `d = 2` polygon `f`-vector equivalence to:
(1) `3 ≤ faceCount P 0` for every 2-polytope `P`,
(2) `faceCount P 1 = faceCount P 0` for every 2-polytope `P`, and
(3) existence of a 2-polytope `P` with `faceCount P 0 = n + 3` for every `n : ℕ`. -/
theorem dim_two_f_vector_iff_of_edge_eq_vertex_and_realization
    (hMinVert : ∀ P : Set (Fin 2 → ℝ), IsDPolytope P → 3 ≤ faceCount P 0)
    (hEdgeEqVert : ∀ P : Set (Fin 2 → ℝ), IsDPolytope P → faceCount P 1 = faceCount P 0)
    (hRealize2 : ∀ n : ℕ, ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3)
    (f : Fin (2 + 1) → ℤ) (_hf0 : f 0 = 1) :
    ((∃ P : Set (Fin 2 → ℝ),
      IsDPolytope P ∧
      ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
     ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3) := by
  constructor
  · rintro ⟨P, hP, hf⟩
    have h3 : 3 ≤ faceCount P 0 := hMinVert P hP
    have h10 : faceCount P 1 = faceCount P 0 := hEdgeEqVert P hP
    refine ⟨faceCount P 0 - 3, ?_, ?_⟩
    · have hf1 := hf 0
      change f 1 = (faceCount P 0 : ℤ) at hf1
      omega
    · have hf2 := hf 1
      change f 2 = (faceCount P 1 : ℤ) at hf2
      omega
  · rintro ⟨n, hf1, hf2⟩
    obtain ⟨P, hP, hn0⟩ := hRealize2 n
    have h10 : faceCount P 1 = faceCount P 0 := hEdgeEqVert P hP
    refine ⟨P, hP, ?_⟩
    intro j
    fin_cases j
    · change f 1 = (faceCount P 0 : ℤ)
      omega
    · change f 2 = (faceCount P 1 : ℤ)
      omega

/-- Reduction of the `d = 3` simplicial Steinitz `f`-vector equivalence to:
(1) `4 ≤ faceCount P 0` for every simplicial 3-polytope `P`,
(2) Euler's relation `faceCount P 0 + faceCount P 2 = faceCount P 1 + 2` and facet-edge double counting
`3 * faceCount P 2 = 2 * faceCount P 1`, and
(3) existence of a simplicial 3-polytope `P` with `faceCount P 0 = n + 4` for every `n : ℕ`. -/
theorem dim_three_f_vector_iff_of_euler_double_count_and_realization
    (hMinVert : ∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P → 4 ≤ faceCount P 0)
    (hEulerAndDouble : ∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P →
      faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1)
    (hRealize3 : ∀ n : ℕ, ∃ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = n + 4)
    (f : Fin (3 + 1) → ℤ) (_hf0 : f 0 = 1) :
    ((∃ P : Set (Fin 3 → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
     ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4) := by
  constructor
  · rintro ⟨P, hP, hf⟩
    have h4 : 4 ≤ faceCount P 0 := hMinVert P hP
    obtain ⟨hEuler, hDouble⟩ := hEulerAndDouble P hP
    refine ⟨faceCount P 0 - 4, ?_, ?_, ?_⟩
    · have hf1 := hf 0
      change f 1 = (faceCount P 0 : ℤ) at hf1
      omega
    · have hf2 := hf 1
      change f 2 = (faceCount P 1 : ℤ) at hf2
      omega
    · have hf3 := hf 2
      change f 3 = (faceCount P 2 : ℤ) at hf3
      omega
  · rintro ⟨n, hf1, hf2, hf3⟩
    obtain ⟨P, hP, hn0⟩ := hRealize3 n
    obtain ⟨hEuler, hDouble⟩ := hEulerAndDouble P hP
    refine ⟨P, hP, ?_⟩
    intro j
    fin_cases j
    · change f 1 = (faceCount P 0 : ℤ)
      omega
    · change f 2 = (faceCount P 1 : ℤ)
      omega
    · change f 3 = (faceCount P 2 : ℤ)
      omega

/-- Reduction of the `d ≥ 4` higher-dimensional `g`-theorem equivalence to necessity and sufficiency
on `faceCount P j.val` (`j : Fin d`). -/
theorem higher_dim_f_vector_iff_of_necessity_and_sufficiency
    (d : ℕ) (_hd : 4 ≤ d)
    (hNec : ∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val)
    (hSuf : ∀ g : ℕ → ℕ, IsMSequence (d / 2) g →
      ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    ((∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
     ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val) := by
  constructor
  · rintro ⟨P, hP, hf⟩
    obtain ⟨g, hg, hgj⟩ := hNec P hP
    refine ⟨g, hg, ?_⟩
    intro k
    refine Fin.cases ?_ ?_ k
    · change f 0 = ∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0
      rw [hf0, gTheoremMatrix_sum_col_zero d g hg.1]
    · intro j
      rw [hf j, hgj j]
  · rintro ⟨g, hg, hfk⟩
    obtain ⟨P, hP, hPj⟩ := hSuf g hg
    refine ⟨P, hP, ?_⟩
    intro j
    rw [hfk j.succ, hPj j]

end Grunbaum2003

namespace Grunbaum2003

theorem g_theorem_f_vector_equivalences_from_geometric_core_proved :
  ((∀ P : Set (Fin 2 → ℝ), IsDPolytope P → 3 ≤ faceCount P 0) →
    (∀ P : Set (Fin 2 → ℝ), IsDPolytope P → faceCount P 1 = faceCount P 0) →
    (∀ n : ℕ, ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3) →
    ∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsDPolytope P ∧
        ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3)) ∧
  ((∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P → 4 ≤ faceCount P 0) →
    (∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P →
      faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1) →
    (∀ n : ℕ, ∃ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = n + 4) →
    ∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 3 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4)) ∧
  (∀ (d : ℕ), 4 ≤ d →
    (∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
    (∀ g : ℕ → ℕ, IsMSequence (d / 2) g →
      ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
    ∀ (f : Fin (d + 1) → ℤ), f 0 = 1 →
      ((∃ P : Set (Fin d → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ k : Fin (d + 1),
          f k = ∑ j ∈ Finset.range (d / 2 + 1),
            (g j : ℤ) * gTheoremMatrix d j k.val)) := by
  refine ⟨dim_two_f_vector_iff_of_edge_eq_vertex_and_realization,
    dim_three_f_vector_iff_of_euler_double_count_and_realization,
    higher_dim_f_vector_iff_of_necessity_and_sufficiency⟩

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  ((∀ P : Set (Fin 2 → ℝ), IsDPolytope P → 3 ≤ faceCount P 0) →
    (∀ P : Set (Fin 2 → ℝ), IsDPolytope P → faceCount P 1 = faceCount P 0) →
    (∀ n : ℕ, ∃ P : Set (Fin 2 → ℝ), IsDPolytope P ∧ faceCount P 0 = n + 3) →
    ∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsDPolytope P ∧
        ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3)) ∧
  ((∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P → 4 ≤ faceCount P 0) →
    (∀ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P →
      faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1) →
    (∀ n : ℕ, ∃ P : Set (Fin 3 → ℝ), IsSimplicialDPolytope P ∧ faceCount P 0 = n + 4) →
    ∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 3 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4)) ∧
  (∀ (d : ℕ), 4 ≤ d →
    (∀ P : Set (Fin d → ℝ), IsSimplicialDPolytope P →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
    (∀ g : ℕ → ℕ, IsMSequence (d / 2) g →
      ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
    ∀ (f : Fin (d + 1) → ℤ), f 0 = 1 →
      ((∃ P : Set (Fin d → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ k : Fin (d + 1),
          f k = ∑ j ∈ Finset.range (d / 2 + 1),
            (g j : ℤ) * gTheoremMatrix d j k.val)) :=
  Grunbaum2003.g_theorem_f_vector_equivalences_from_geometric_core_proved
