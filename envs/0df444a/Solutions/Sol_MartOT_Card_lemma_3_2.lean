-- Prove2me | solution 1 for MartOT.Card.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:18:57.479024+00:00
-- url     : https://prove2.me/submissions/ae16460b-29b3-427d-bc1c-96467be677f1

import Mathlib

namespace Mot8L32

/-- Points of `A` that are right-isolated for the graph of `F` form a countable set. -/
lemma right_isolated_countable {X : Type} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] (A : Set ℝ) (F : ℝ → X) :
    {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a < a' → a' < a + ε → ε ≤ dist (F a') (F a)}.Countable := by
  classical
  set R := {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a < a' → a' < a + ε → ε ≤ dist (F a') (F a)}
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable D := hDc.to_subtype
  have hch : ∀ x : R, ∃ (ε : ℝ) (r s : ℚ) (d : D), 0 < (r : ℝ) ∧ (r : ℝ) < ε / 2 ∧
      x.1 < s ∧ (s : ℝ) < x.1 + ε ∧ dist (F x.1) d < r ∧
      ∀ a' ∈ A, x.1 < a' → a' < x.1 + ε → ε ≤ dist (F a') (F x.1) := by
    intro x
    obtain ⟨_, ε, hε, hiso⟩ := x.2
    obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by linarith)
    obtain ⟨s, hs0, hs1⟩ := exists_rat_btwn (show x.1 < x.1 + ε by linarith)
    obtain ⟨d, hdD, hd⟩ := hDd.exists_dist_lt (F x.1) hr0
    exact ⟨ε, r, s, ⟨d, hdD⟩, hr0, hr1, hs0, hs1, hd, hiso⟩
  choose ε r s d hr0 hr1 hs0 hs1 hd hiso using hch
  let g : R → ℚ × ℚ × D := fun x => (r x, s x, d x)
  have key : ∀ x y : R, g x = g y → x.1 < y.1 → False := by
    intro x y hxy hlt
    simp only [g, Prod.mk.injEq] at hxy
    obtain ⟨hr, hs, hdd⟩ := hxy
    have h1 := hiso x y.1 y.2.1 hlt (by
      have := hs0 y; rw [← hs] at this; linarith [hs1 x])
    have h2 := hd y
    rw [← hdd, ← hr] at h2
    have h3 := dist_triangle (F y.1) (d x) (F x.1)
    have h4 := hd x
    rw [dist_comm] at h4
    linarith [hr1 x]
  have hinj : Function.Injective g := by
    intro x y hxy
    rcases lt_trichotomy x.1 y.1 with h | h | h
    · exact (key x y hxy h).elim
    · exact Subtype.ext h
    · exact (key y x hxy.symm h).elim
  exact Set.countable_coe_iff.1 hinj.countable

/-- Points of `A` that are left-isolated for the graph of `F` form a countable set. -/
lemma left_isolated_countable {X : Type} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] (A : Set ℝ) (F : ℝ → X) :
    {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a' < a → a - ε < a' → ε ≤ dist (F a') (F a)}.Countable := by
  classical
  set R := {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a' < a → a - ε < a' → ε ≤ dist (F a') (F a)}
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable D := hDc.to_subtype
  have hch : ∀ x : R, ∃ (ε : ℝ) (r s : ℚ) (d : D), 0 < (r : ℝ) ∧ (r : ℝ) < ε / 2 ∧
      (s : ℝ) < x.1 ∧ x.1 - ε < s ∧ dist (F x.1) d < r ∧
      ∀ a' ∈ A, a' < x.1 → x.1 - ε < a' → ε ≤ dist (F a') (F x.1) := by
    intro x
    obtain ⟨_, ε, hε, hiso⟩ := x.2
    obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by linarith)
    obtain ⟨s, hs0, hs1⟩ := exists_rat_btwn (show x.1 - ε < x.1 by linarith)
    obtain ⟨d, hdD, hd⟩ := hDd.exists_dist_lt (F x.1) hr0
    exact ⟨ε, r, s, ⟨d, hdD⟩, hr0, hr1, hs1, hs0, hd, hiso⟩
  choose ε r s d hr0 hr1 hs0 hs1 hd hiso using hch
  let g : R → ℚ × ℚ × D := fun x => (r x, s x, d x)
  have key : ∀ x y : R, g x = g y → y.1 < x.1 → False := by
    intro x y hxy hlt
    simp only [g, Prod.mk.injEq] at hxy
    obtain ⟨hr, hs, hdd⟩ := hxy
    have h1 := hiso x y.1 y.2.1 hlt (by
      have := hs0 y; rw [← hs] at this; linarith [hs1 x])
    have h2 := hd y
    rw [← hdd, ← hr] at h2
    have h3 := dist_triangle (F y.1) (d x) (F x.1)
    have h4 := hd x
    rw [dist_comm] at h4
    linarith [hr1 x]
  have hinj : Function.Injective g := by
    intro x y hxy
    rcases lt_trichotomy x.1 y.1 with h | h | h
    · exact (key y x hxy.symm h).elim
    · exact Subtype.ext h
    · exact (key x y hxy h).elim
  exact Set.countable_coe_iff.1 hinj.countable

end Mot8L32

open Mot8L32 in
theorem solution (k : ℕ) (hk : 0 < k) (Γ : Set (ℝ × ℝ))
    (hΓ : ¬ {a : ℝ | (k : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard}.Countable) :
    ∃ (a : ℝ) (b : Fin k → ℝ), StrictMono b ∧ (∀ i, (a, b i) ∈ Γ) ∧
      ∀ ε : ℝ, 0 < ε →
        (∃ a' : ℝ, a < a' ∧ ∃ b' : Fin k → ℝ, StrictMono b' ∧ (∀ i, (a', b' i) ∈ Γ) ∧
          |a - a'| < ε ∧ ∀ i, |b i - b' i| < ε) ∧
        (∃ a'' : ℝ, a'' < a ∧ ∃ b'' : Fin k → ℝ, StrictMono b'' ∧ (∀ i, (a'', b'' i) ∈ Γ) ∧
          |a - a''| < ε ∧ ∀ i, |b i - b'' i| < ε) := by
  classical
  set A := {a : ℝ | (k : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard}
  have hex : ∀ a ∈ A, ∃ b : Fin k → ℝ, StrictMono b ∧ ∀ i, (a, b i) ∈ Γ := by
    intro a ha
    obtain ⟨t, hts, htk⟩ := Set.exists_subset_encard_eq ha
    have htf : t.Finite := Set.finite_of_encard_eq_coe htk
    have hcard : htf.toFinset.card = k := by
      rw [htf.encard_eq_coe_toFinset_card] at htk
      exact_mod_cast htk
    refine ⟨fun i => htf.toFinset.orderEmbOfFin hcard i,
      (htf.toFinset.orderEmbOfFin hcard).strictMono, fun i => ?_⟩
    have := htf.toFinset.orderEmbOfFin_mem hcard i
    rw [Set.Finite.mem_toFinset] at this
    exact hts this
  let F : ℝ → (Fin k → ℝ) := fun a => if h : a ∈ A then Classical.choose (hex a h) else 0
  have hF : ∀ a ∈ A, StrictMono (F a) ∧ ∀ i, (a, F a i) ∈ Γ := by
    intro a ha
    simp only [F, dif_pos ha]
    exact Classical.choose_spec (hex a ha)
  have hR := right_isolated_countable A F
  have hL := left_isolated_countable A F
  have hne : (A \ ({a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a < a' → a' < a + ε → ε ≤ dist (F a') (F a)} ∪
      {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a' < a → a - ε < a' → ε ≤ dist (F a') (F a)})).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hemp
    exact hΓ ((hR.union hL).mono hemp)
  obtain ⟨a, haA, hnot⟩ := hne
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_exists, not_forall,
    not_le] at hnot
  obtain ⟨hnR, hnL⟩ := hnot
  refine ⟨a, F a, (hF a haA).1, (hF a haA).2, fun ε hε => ⟨?_, ?_⟩⟩
  · obtain ⟨a', ha'A, hlt, hlt2, hd⟩ := hnR haA ε hε
    refine ⟨a', hlt, F a', (hF a' ha'A).1, (hF a' ha'A).2, ?_, fun i => ?_⟩
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [← Real.dist_eq, dist_comm]
      exact lt_of_le_of_lt (dist_le_pi_dist (F a') (F a) i) hd
  · obtain ⟨a', ha'A, hlt, hlt2, hd⟩ := hnL haA ε hε
    refine ⟨a', hlt, F a', (hF a' ha'A).1, (hF a' ha'A).2, ?_, fun i => ?_⟩
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [← Real.dist_eq, dist_comm]
      exact lt_of_le_of_lt (dist_le_pi_dist (F a') (F a) i) hd
