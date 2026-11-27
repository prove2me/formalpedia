-- Prove2me | solution 1 for MetricTSPSublinear.lemma_5_1_fragment_size
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:05:35.965743+00:00
-- url     : https://prove2.me/submissions/031eab7c-a448-4c78-b96d-6bbabf570a68

import Mathlib
import Definitions.Def_MetricTSPSublinear_fragments
import Theorems.Thm_MetricTSPSublinear_sample_hits_large_sets

/-!
# Fragments of a rooted forest after removing `Fsplit` (§5.1, §9.1 of Azarmehr–Behnezhad)

A rooted forest on `Fin n` is a parent map `par` with root set `R` (`par r = r` on `R`) and a rank
function strictly decreasing along `par` off `R`.  For a sample set `S`,
`Fsplit = R ∪ {ancestors-or-self of sampled vertices}`; the fragments are the classes of the
equivalence closure of the parent relation restricted to non-`Fsplit` vertices.
-/

namespace MTSPFR
open MetricTSPSublinear.Fragments

open Finset

noncomputable section
open Classical

variable {n : ℕ}

/-- The top vertex of `u`: `par^[m] u` for the least `m` with `par (par^[m] u) ∈ F`. -/
def top (par : Fin n → Fin n) (F : Finset (Fin n)) (u : Fin n) : Fin n :=
  if h : ∃ j, par (par^[j] u) ∈ F then par^[Nat.find h] u else u

lemma anc_refl (par : Fin n → Fin n) (u : Fin n) : Anc par u u := ⟨0, rfl⟩

lemma anc_par (par : Fin n → Fin n) (u : Fin n) : Anc par u (par u) := ⟨1, rfl⟩

lemma anc_trans {par : Fin n → Fin n} {a b c : Fin n} (h1 : Anc par a b) (h2 : Anc par b c) :
    Anc par a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  exact ⟨j + i, Function.iterate_add_apply _ _ _ _⟩

section Forest

variable (par : Fin n → Fin n) (rank : Fin n → ℕ) (R : Finset (Fin n))
  (hR : ∀ r ∈ R, par r = r) (hrank : ∀ v, v ∉ R → rank (par v) < rank v)
include hR

/-- `Fsplit` is closed upward. -/
lemma Fsplit_up (S : Finset (Fin n)) {w x : Fin n} (hw : w ∈ Fsplit par R S)
    (hwx : Anc par w x) : x ∈ Fsplit par R S := by
  unfold Fsplit at hw ⊢
  rcases mem_union.1 hw with h | h
  · obtain ⟨k, rfl⟩ := hwx
    rw [Function.iterate_fixed (hR w h)]
    exact mem_union_left _ h
  · obtain ⟨y, hy, hyw⟩ := (mem_filter.1 h).2
    exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, y, hy, anc_trans hyw hwx⟩)

omit hR in
include hrank in
lemma reach_root : ∀ u, ∃ k, par^[k] u ∈ R := by
  intro u
  induction h : rank u using Nat.strong_induction_on generalizing u with
  | _ m ih =>
    by_cases hu : u ∈ R
    · exact ⟨0, hu⟩
    · obtain ⟨k, hk⟩ := ih (rank (par u)) (h ▸ hrank u hu) (par u) rfl
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

include hrank in
lemma top_exists (S : Finset (Fin n)) (u : Fin n) :
    ∃ j, par (par^[j] u) ∈ Fsplit par R S := by
  obtain ⟨k, hk⟩ := reach_root par rank R hrank u
  exact ⟨k, by rw [hR _ hk]; exact mem_union_left _ hk⟩

include hrank in
lemma top_spec (S : Finset (Fin n)) (u : Fin n) (hu : u ∉ Fsplit par R S) :
    Anc par u (top par (Fsplit par R S) u) ∧ top par (Fsplit par R S) u ∉ Fsplit par R S ∧
      par (top par (Fsplit par R S) u) ∈ Fsplit par R S := by
  have hex := top_exists par rank R hR hrank S u
  have ht : top par (Fsplit par R S) u = par^[Nat.find hex] u := by
    unfold top; rw [dif_pos hex]
  rw [ht]
  refine ⟨⟨_, rfl⟩, ?_, Nat.find_spec hex⟩
  rcases hm : Nat.find hex with _ | i
  · simpa using hu
  · have := Nat.find_min hex (show i < Nat.find hex by omega)
    rwa [Function.iterate_succ_apply']

lemma exit_unique (S : Finset (Fin n)) {u x y : Fin n} (hx : Anc par u x) (hy : Anc par u y)
    (hxF : x ∉ Fsplit par R S) (hyF : y ∉ Fsplit par R S)
    (hpx : par x ∈ Fsplit par R S) (hpy : par y ∈ Fsplit par R S) : x = y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  rcases lt_trichotomy i j with h | h | h
  · exfalso; apply hyF
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    refine Fsplit_up par R hR S hpx ⟨d, ?_⟩
    rw [← Function.iterate_succ_apply' par i, ← Function.iterate_add_apply]
    congr 1; omega
  · rw [h]
  · exfalso; apply hxF
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    refine Fsplit_up par R hR S hpy ⟨d, ?_⟩
    rw [← Function.iterate_succ_apply' par j, ← Function.iterate_add_apply]
    congr 1; omega

include hrank in
/-- The top vertex is the unique ancestor-or-self outside `Fsplit` whose parent is in `Fsplit`. -/
lemma top_unique (S : Finset (Fin n)) {u x : Fin n} (hu : u ∉ Fsplit par R S)
    (hx : Anc par u x) (hxF : x ∉ Fsplit par R S) (hpx : par x ∈ Fsplit par R S) :
    x = top par (Fsplit par R S) u := by
  obtain ⟨h1, h2, h3⟩ := top_spec par rank R hR hrank S u hu
  exact exit_unique par R hR S hx h1 hxF h2 hpx h3

/-- A subtree rooted outside `Fsplit` avoids `Fsplit`. -/
lemma sub_disjoint (S : Finset (Fin n)) {x w : Fin n} (hx : x ∉ Fsplit par R S)
    (hw : w ∈ sub par x) : w ∉ Fsplit par R S := fun hwF =>
  hx (Fsplit_up par R hR S hwF (mem_filter.1 hw).2)

include hrank in
/-- The subtree of the top vertex contains no sampled vertex. -/
lemma no_sample_in_sub_top (S : Finset (Fin n)) {u : Fin n} (hu : u ∉ Fsplit par R S) :
    ∀ x ∈ S, x ∉ sub par (top par (Fsplit par R S) u) := by
  intro x hxS hx
  apply (top_spec par rank R hR hrank S u hu).2.1
  exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, x, hxS, (mem_filter.1 hx).2⟩)

lemma eqv_of_anc (S : Finset (Fin n)) :
    ∀ (k : ℕ) (w : Fin n), par^[k] w ∉ Fsplit par R S →
      Relation.EqvGen (FragRel par (Fsplit par R S)) w (par^[k] w) := by
  intro k
  induction k with
  | zero => intro w _; exact Relation.EqvGen.refl _
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply] at hw ⊢
    have hpw : par w ∉ Fsplit par R S := fun h => hw (Fsplit_up par R hR S h ⟨k, rfl⟩)
    have hw0 : w ∉ Fsplit par R S := fun h => hpw (Fsplit_up par R hR S h (anc_par par w))
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hw0, hpw, rfl⟩) (ih _ hw)

include hrank in
/-- **Fragments are subtrees of top vertices.** For `u ∉ Fsplit`, the fragment of `u` (its class
under the equivalence closure of parent edges among non-`Fsplit` vertices) is `sub (top u)`. -/
theorem frag_eq_sub_top (S : Finset (Fin n)) (u : Fin n) (hu : u ∉ Fsplit par R S) :
    frag par (Fsplit par R S) u = sub par (top par (Fsplit par R S) u) := by
  set F := Fsplit par R S with hF
  ext w
  simp only [frag, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have key : ∀ a b, Relation.EqvGen (FragRel par F) a b →
        a = b ∨ (a ∉ F ∧ b ∉ F ∧ top par F a = top par F b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        obtain ⟨ha, hb, rfl⟩ := hab
        right
        refine ⟨ha, hb, ?_⟩
        obtain ⟨h1, h2, h3⟩ := top_spec par rank R hR hrank S (par a) hb
        exact (top_unique par rank R hR hrank S ha (anc_trans (anc_par par a) h1) h2 h3).symm
      | refl a => exact Or.inl rfl
      | symm a b _ ih =>
        rcases ih with h | ⟨h1, h2, h3⟩
        · exact Or.inl h.symm
        · exact Or.inr ⟨h2, h1, h3.symm⟩
      | trans a b c _ _ ih1 ih2 =>
        rcases ih1 with rfl | ⟨h1, h2, h3⟩
        · exact ih2
        · rcases ih2 with rfl | ⟨h4, h5, h6⟩
          · exact Or.inr ⟨h1, h2, h3⟩
          · exact Or.inr ⟨h1, h5, h3.trans h6⟩
    rcases key u w h with rfl | ⟨_, hw, ht⟩
    · exact mem_filter.2 ⟨mem_univ _, (top_spec par rank R hR hrank S _ hu).1⟩
    · rw [ht]; exact mem_filter.2 ⟨mem_univ _, (top_spec par rank R hR hrank S w hw).1⟩
  · intro hw
    obtain ⟨h1, h2, _⟩ := top_spec par rank R hR hrank S u hu
    obtain ⟨k, hk⟩ := (mem_filter.1 hw).2
    obtain ⟨j, hj⟩ := h1
    have e1 := eqv_of_anc par R hR S k w (hk ▸ h2)
    have e2 := eqv_of_anc par R hR S j u (hj ▸ h2)
    rw [hk] at e1; rw [hj] at e2
    exact Relation.EqvGen.trans _ _ _ e2 (Relation.EqvGen.symm _ _ e1)

include hrank in
/-- **(1) Deterministic.** If every subtree with at least `k` vertices contains a sampled vertex,
then every fragment has fewer than `k` vertices. -/
theorem fragments_small (S : Finset (Fin n)) (k : ℕ)
    (hhit : ∀ v, k ≤ (sub par v).card → ∃ x ∈ S, x ∈ sub par v) :
    ∀ u, u ∉ Fsplit par R S → (frag par (Fsplit par R S) u).card < k := by
  intro u hu
  rw [frag_eq_sub_top par rank R hR hrank S u hu]
  by_contra h
  obtain ⟨x, hxS, hx⟩ := hhit _ (not_lt.1 h)
  exact no_sample_in_sub_top par rank R hR hrank S hu x hxS hx

include hrank in
/-- **(2) Probabilistic (counting form).** Among the `n^s` sample tuples `σ : Fin s → Fin n`
(`S = image σ`), at most `n · n^s · exp(-k s / n)` produce some fragment with `≥ k` vertices. -/
theorem fragments_large_count (s k : ℕ) :
    ((univ.filter (fun σ : Fin s → Fin n => ∃ u, u ∉ Fsplit par R (univ.image σ) ∧
        k ≤ (frag par (Fsplit par R (univ.image σ)) u).card)).card : ℝ) ≤
      (n : ℝ) * ((n : ℝ) ^ s * Real.exp (-(k : ℝ) * s / n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (univ.filter (fun σ : Fin s → Fin 0 => ∃ u, u ∉ Fsplit par R (univ.image σ) ∧
        k ≤ (frag par (Fsplit par R (univ.image σ)) u).card)) = ∅ := by
      ext σ; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨u, _⟩; exact u.elim0
    rw [this]; simp
  let J := {v : Fin n // k ≤ (sub par v).card}
  have hmain := MetricTSPSublinear.sample_hits_large_sets (J := J) n s k hn
    (fun j => sub par j.1) (fun j => j.2)
  have hJ : (Fintype.card J : ℝ) ≤ n := by
    have := Fintype.card_subtype_le (fun v : Fin n => k ≤ (sub par v).card)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hsub : (univ.filter (fun σ : Fin s → Fin n => ∃ u, u ∉ Fsplit par R (univ.image σ) ∧
        k ≤ (frag par (Fsplit par R (univ.image σ)) u).card)) ⊆
      (univ.filter (fun σ : Fin s → Fin n => ∃ j : J, ∀ i, σ i ∉ sub par j.1)) := by
    intro σ hσ
    obtain ⟨u, hu, hk⟩ := (mem_filter.1 hσ).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    by_contra hno
    push Not at hno
    have hhit : ∀ v, k ≤ (sub par v).card → ∃ x ∈ univ.image σ, x ∈ sub par v := by
      intro v hv
      obtain ⟨i, hi⟩ := hno ⟨v, hv⟩
      exact ⟨σ i, mem_image_of_mem _ (mem_univ _), hi⟩
    have := fragments_small par rank R hR hrank (univ.image σ) k hhit u hu
    omega
  have hc := Finset.card_le_card hsub
  calc _ ≤ ((univ.filter (fun σ : Fin s → Fin n => ∃ j : J, ∀ i, σ i ∉ sub par j.1)).card : ℝ) := by
        exact_mod_cast hc
    _ ≤ (Fintype.card J : ℝ) * ((n : ℝ) ^ s * Real.exp (-(k : ℝ) * s / n)) := by
        convert hmain using 3
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right hJ
        positivity

end Forest

end

end MTSPFR

open MetricTSPSublinear.Fragments in
theorem solution {n : ℕ} (par : Fin n → Fin n) (rank : Fin n → ℕ) (R : Finset (Fin n))
    (hR : ∀ r ∈ R, par r = r) (hrank : ∀ v, v ∉ R → rank (par v) < rank v) (s k : ℕ) :
    ((Finset.univ.filter (fun σ : Fin s → Fin n => ∃ u, u ∉ Fsplit par R (Finset.univ.image σ) ∧
        k ≤ (frag par (Fsplit par R (Finset.univ.image σ)) u).card)).card : ℝ) ≤
      (n : ℝ) * ((n : ℝ) ^ s * Real.exp (-(k : ℝ) * s / n)) :=
  MTSPFR.fragments_large_count par rank R hR hrank s k
