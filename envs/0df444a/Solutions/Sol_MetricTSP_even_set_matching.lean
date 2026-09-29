-- Prove2me | solution 1 for MetricTSP.even_set_matching
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-25T05:13:05.206533+00:00
-- url     : https://prove2.me/submissions/c1876bb4-2065-4c9f-89fd-5239ef1ee4c9

import Mathlib
import Definitions.Def_MetricTSP_model
import Theorems.Thm_MetricTSP_pm_polytope_decomposition

set_option maxHeartbeats 1000000

namespace MetricTSP

variable {n : ℕ}

/-- Swap a `Finset` sum with a `List.map`-sum. -/
lemma sum_list_swap {α : Type} {β : Type} (L : List α) (s : Finset β)
    (F : α → β → ℝ) :
    ∑ b ∈ s, (L.map (fun a => F a b)).sum
      = (L.map (fun a => ∑ b ∈ s, F a b)).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

/-- Every nonempty list has a minimizer of any real-valued function. -/
lemma list_argmin {α : Type} (f : α → ℝ) :
    ∀ L : List α, L ≠ [] → ∃ p ∈ L, ∀ q ∈ L, f p ≤ f q := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    by_cases hl : l = []
    · subst hl
      exact ⟨a, List.mem_cons_self, by
        intro q hq
        rw [List.mem_singleton] at hq
        rw [hq]⟩
    · obtain ⟨p, hp, hmin⟩ := ih hl
      by_cases hle : f a ≤ f p
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with h | h
        · rw [h]
        · exact le_trans hle (hmin q h)
      · refine ⟨p, List.mem_cons_of_mem a hp, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with h | h
        · rw [h]; linarith
        · exact hmin q h

/-- Factor a constant out of a mapped list sum. -/
lemma list_sum_mul_const {α : Type} (L : List α) (g : α → ℝ) (K : ℝ) :
    (L.map (fun a => g a * K)).sum = (L.map g).sum * K := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

lemma list_sum_le_sum {α : Type} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, f a ≤ g a) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    linarith

theorem even_set_matching_thm (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (W : Finset (Fin n)) (hW : Even W.card) (hWn : W.Nonempty)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hcut : ∀ S : Finset (Fin n), S ⊆ W → S.Nonempty → S ≠ W →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ f : Fin n → Fin n, (∀ v ∈ W, f v ∈ W ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ W, f v = v) ∧
      ∑ v ∈ W, c v (f v) ≤ ∑ u, ∑ v, y u v * c u v := by
  classical
  -- odd cuts follow from the full cut hypothesis
  have hodd : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v := by
    intro S hSW hSodd
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h, Finset.card_empty] at hSodd
      exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hSodd
    have hSne : S ≠ W := by
      intro h
      rw [h] at hSodd
      exact (Nat.not_odd_iff_even.mpr hW) hSodd
    exact hcut S hSW hne hSne
  obtain ⟨L, hLne, hLmem, hLsum, hLdec⟩ :=
    pm_polytope_decomposition n W hW y hsym hnn hdiag hsupp hdeg hodd
  -- the cost of y is the λ-average of the matching costs
  have hkey : ∑ u, ∑ v, y u v * c u v
      = (L.map (fun p => p.1 * ∑ v ∈ W, c v (p.2 v))).sum := by
    have h1 : ∀ u v : Fin n, y u v * c u v
        = (L.map (fun p => (if p.2 u = v ∧ u ∈ W then p.1 else 0) * c u v)).sum := by
      intro u v
      rw [hLdec u v, ← list_sum_mul_const L
        (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0) (c u v)]
    have h2 : ∑ u, ∑ v, y u v * c u v
        = (L.map (fun p => ∑ u, ∑ v,
            (if p.2 u = v ∧ u ∈ W then p.1 else 0) * c u v)).sum := by
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) =>
        Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => h1 u v))]
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) =>
        sum_list_swap L Finset.univ
          (fun p v => (if p.2 u = v ∧ u ∈ W then p.1 else 0) * c u v))]
      exact sum_list_swap L Finset.univ (fun p u => ∑ v,
        (if p.2 u = v ∧ u ∈ W then p.1 else 0) * c u v)
    rw [h2]
    congr 1
    refine List.map_congr_left (fun p hp => ?_)
    -- for a fixed pairing: the double sum collapses to its matching cost
    have h3 : ∀ u : Fin n, ∑ v, (if p.2 u = v ∧ u ∈ W then p.1 else 0) * c u v
        = if u ∈ W then p.1 * c u (p.2 u) else 0 := by
      intro u
      by_cases huW : u ∈ W
      · rw [if_pos huW]
        rw [Finset.sum_eq_single (p.2 u)]
        · rw [if_pos ⟨rfl, huW⟩]
        · intro v _ hv
          rw [if_neg (fun hh => hv (hh.1.symm))]
          ring
        · intro h
          exact absurd (Finset.mem_univ (p.2 u)) h
      · rw [if_neg huW]
        refine Finset.sum_eq_zero (fun v _ => ?_)
        rw [if_neg (fun hh => huW hh.2)]
        ring
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => h3 u),
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.mul_sum]
  obtain ⟨p₀, hp₀L, hp₀min⟩ :=
    list_argmin (fun p : ℝ × (Fin n → Fin n) => ∑ v ∈ W, c v (p.2 v)) L hLne
  obtain ⟨hp₀pos, hp₀pair, hp₀fix⟩ := hLmem p₀ hp₀L
  refine ⟨p₀.2, hp₀pair, hp₀fix, ?_⟩
  have h4 : ∀ p ∈ L, p.1 * (∑ v ∈ W, c v (p₀.2 v))
      ≤ p.1 * (∑ v ∈ W, c v (p.2 v)) := by
    intro p hp
    exact mul_le_mul_of_nonneg_left (hp₀min p hp) (le_of_lt (hLmem p hp).1)
  have h5 : (L.map (fun p => p.1 * (∑ v ∈ W, c v (p₀.2 v)))).sum
      ≤ (L.map (fun p => p.1 * (∑ v ∈ W, c v (p.2 v)))).sum :=
    list_sum_le_sum L _ _ h4
  have h6 : (L.map (fun p => p.1 * (∑ v ∈ W, c v (p₀.2 v)))).sum
      = ∑ v ∈ W, c v (p₀.2 v) := by
    rw [list_sum_mul_const L Prod.fst (∑ v ∈ W, c v (p₀.2 v)), hLsum, one_mul]
  rw [hkey]
  linarith

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (W : Finset (Fin n)) (hW : Even W.card) (hWn : W.Nonempty)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hcut : ∀ S : Finset (Fin n), S ⊆ W → S.Nonempty → S ≠ W →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ f : Fin n → Fin n, (∀ v ∈ W, f v ∈ W ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ W, f v = v) ∧
      ∑ v ∈ W, c v (f v) ≤ ∑ u, ∑ v, y u v * c u v :=
  MetricTSP.even_set_matching_thm c hc W hW hWn y hsym hnn hdiag hsupp hdeg hcut
