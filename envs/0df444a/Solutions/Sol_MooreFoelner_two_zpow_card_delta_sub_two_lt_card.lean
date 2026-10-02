-- Prove2me | solution 1 for MooreFoelner.two_zpow_card_delta_sub_two_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T07:55:48.198084+00:00
-- url     : https://prove2.me/submissions/db819c7f-969c-495c-8992-ccd6a8398034

import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore §5: the operation `∂` (Lemmas 5.2, 5.4, 5.5)
-/

namespace MooreFoelner.Dev.Delta

open Classical CannonFloydParry MooreFoelner

/-! ## Prefixes and initial parts -/

/-- The infinite sequence extending `u` by zeros. -/
def ext (u : Seq) : ℕ → Bool := fun n => if h : n < u.length then u[n] else false

theorem ip_ext (u : Seq) : IsInitialPart u (ext u) := by
  intro i h
  simp [ext, h]

theorem ip_of_prefix {u v : Seq} {x : ℕ → Bool} (hv : IsInitialPart v x) (h : u <+: v) :
    IsInitialPart u x := by
  intro i hi
  have hl := h.length_le
  have := hv i (by omega)
  simp only [List.get_eq_getElem] at this ⊢
  rw [← this, h.getElem hi]

/-! ## Trees -/

theorem tr_ip {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT x
  exact ⟨t, ht, hx⟩

theorem tr_unique {T : Finset Seq} (hT : IsTree T) {x : ℕ → Bool} {t t' : Seq} (ht : t ∈ T)
    (hx : IsInitialPart t x) (ht' : t' ∈ T) (hx' : IsInitialPart t' x) : t = t' := by
  obtain ⟨s, -, hs⟩ := hT x
  rw [hs t ⟨ht, hx⟩, hs t' ⟨ht', hx'⟩]

theorem tr_eq {T : Finset Seq} (hT : IsTree T) {u v : Seq} (hu : u ∈ T)
    (hv : v ∈ T) (h : u <+: v) : u = v :=
  tr_unique hT hu (ip_of_prefix (ip_ext v) h) hv (ip_ext v)

theorem tr_nonempty {T : Finset Seq} (hT : IsTree T) : T.Nonempty := by
  obtain ⟨t, ht, -⟩ := tr_ip hT (fun _ => false)
  exact ⟨t, ht⟩

theorem sum_card_filter_le (U T : Finset Seq) (hU : ∀ u ∈ U, ∀ u' ∈ U, u <+: u' → u = u') :
    ∑ u ∈ U, (T.filter (u <+: ·)).card ≤ T.card := by
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro t
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    rintro ⟨_, _, ht, _⟩
    exact ht
  · intro u hu u' hu' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_filter] at ht ht'
    rcases List.prefix_or_prefix_of_prefix ht.2 ht'.2 with h | h
    · exact hne (hU u hu u' hu' h)
    · exact hne (hU u' hu' u hu h).symm

/-! ## The first-difference relation -/

/-! ## Constant sequences -/

/-! ## Quotients `T/u` -/

theorem card_quot (T : Finset Seq) (u : Seq) :
    (quot T u).card = (T.filter (u <+: ·)).card := by
  unfold quot
  apply Finset.card_image_of_injOn
  intro s hs t ht h
  simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ht
  obtain ⟨s', rfl⟩ := hs.2
  obtain ⟨t', rfl⟩ := ht.2
  simp only [List.drop_left] at h
  rw [h]

theorem card_quot_pos (T : Finset Seq) {u : Seq} (h : ∃ t ∈ T, u <+: t) :
    1 ≤ (quot T u).card := by
  rw [card_quot]
  obtain ⟨t, ht, hut⟩ := h
  exact Finset.card_pos.mpr ⟨t, by simp [ht, hut]⟩

/-! ## Sorting -/

theorem mem_sorted {U : Finset Seq} {x : Seq} : x ∈ sorted U ↔ x ∈ U := by
  simp [sorted, List.mem_mergeSort]

theorem sorted_perm (U : Finset Seq) : (sorted U).Perm U.toList := List.mergeSort_perm _ _

theorem length_sorted (U : Finset Seq) : (sorted U).length = U.card := by
  simp [sorted]

theorem sum_sorted (U : Finset Seq) (g : Seq → ℕ) : ((sorted U).map g).sum = ∑ u ∈ U, g u := by
  rw [((sorted_perm U).map g).sum_eq]
  exact Finset.sum_map_toList U g

/-! ## Lists sorted by a strict order -/

/-! ## Interior elements and the semantic form of the conditions -/

theorem interior_sublist (U : Finset Seq) : (interior U).Sublist (sorted U) :=
  (List.dropLast_sublist _).trans (List.drop_sublist _ _)

theorem mem_of_mem_interior {U : Finset Seq} {x : Seq} (h : x ∈ interior U) : x ∈ U :=
  mem_sorted.1 ((interior_sublist U).subset h)

theorem opt_pairwise_iff (T U : Finset Seq) (R : ℕ → ℕ → Prop) :
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      R (quot T ((interior U).get ⟨i, hi⟩)).card (quot T ((interior U).get ⟨j, hj⟩)).card) ↔
      (interior U).Pairwise (fun x y => R (quot T x).card (quot T y).card) := by
  rw [List.pairwise_iff_getElem]
  simp only [List.get_eq_getElem]

/-! ## The join of two trees -/

/-! ## The orientation of condition 2 -/

/-! ## Lemma 5.2 -/

/-! ## Lemma 5.4 -/

theorem geom_sum : ∀ (l : List ℕ) (c : ℕ), l.Pairwise (fun x y => 2 * x ≤ y) →
    (∀ x ∈ l, c ≤ x) → c * 2 ^ l.length ≤ l.sum + c
  | [], c, _, _ => by simp
  | a :: l, c, hl, hc => by
    rw [List.pairwise_cons] at hl
    have hca : c ≤ a := hc a List.mem_cons_self
    have ih := geom_sum l (2 * c) hl.2 (fun y hy => by have := hl.1 y hy; omega)
    simp only [List.length_cons, List.sum_cons, pow_succ]
    have : c * (2 ^ l.length * 2) = 2 * c * 2 ^ l.length := by ring
    rw [this]
    omega

theorem sum_interior_ge {T U : Finset Seq} (hUT : Dominated U T)
    (h2 : (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨i, hi⟩)).card ≤ (quot T ((interior U).get ⟨j, hj⟩)).card) ∨
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨j, hj⟩)).card ≤ (quot T ((interior U).get ⟨i, hi⟩)).card)) :
    2 ^ (interior U).length ≤ ((interior U).map (fun u => (quot T u).card)).sum + 1 := by
  have hpos : ∀ x ∈ (interior U).map (fun u => (quot T u).card), 1 ≤ x := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact card_quot_pos T (hUT u (mem_of_mem_interior hu))
  rcases h2 with h | h
  · rw [opt_pairwise_iff T U (fun a b => 2 * a ≤ b)] at h
    have := geom_sum _ 1 (List.pairwise_map.2 h) hpos
    simpa using this
  · rw [opt_pairwise_iff T U (fun a b => 2 * b ≤ a)] at h
    have h' := List.pairwise_reverse.2 ((List.pairwise_map (R := fun a b => 2 * b ≤ a)).2 h)
    have := geom_sum _ 1 h' (fun x hx => hpos x (List.mem_reverse.1 hx))
    simpa using this

theorem card_bound {T U : Finset Seq} (hU : IsTree U) (hUT : Dominated U T)
    (h2 : (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨i, hi⟩)).card ≤ (quot T ((interior U).get ⟨j, hj⟩)).card) ∨
    (∀ i j (hi : i < (interior U).length) (hj : j < (interior U).length), i < j →
      2 * (quot T ((interior U).get ⟨j, hj⟩)).card ≤ (quot T ((interior U).get ⟨i, hi⟩)).card))
    (hn : 2 ≤ U.card) : 2 ^ (U.card - 2) < T.card := by
  have hsum := sum_card_filter_le U T (fun u hu u' hu' h => tr_eq hU hu hu' h)
  simp_rw [← card_quot] at hsum
  rw [← sum_sorted U (fun u => (quot T u).card)] at hsum
  have hint := sum_interior_ge hUT h2
  have hlen := length_sorted U
  obtain ⟨a, m, hl⟩ : ∃ a m, sorted U = a :: m := by
    cases h : sorted U with
    | nil => rw [h] at hlen; simp at hlen; omega
    | cons a m => exact ⟨a, m, rfl⟩
  have hm : m ≠ [] := by
    rintro rfl
    rw [hl] at hlen
    simp at hlen
    omega
  have hint_eq : interior U = m.dropLast := by
    unfold interior
    rw [hl]
    simp
  have hdecomp : m = m.dropLast ++ [m.getLast hm] := (List.dropLast_append_getLast hm).symm
  have ha : a ∈ U := mem_sorted.1 (by rw [hl]; exact List.mem_cons_self)
  have hz : m.getLast hm ∈ U := mem_sorted.1 (by rw [hl]; exact List.mem_cons_of_mem _ (List.getLast_mem hm))
  have h1 := card_quot_pos T (hUT a ha)
  have h2' := card_quot_pos T (hUT _ hz)
  rw [hl, hdecomp] at hsum
  rw [hint_eq] at hint
  have hlen' : (interior U).length = U.card - 2 := by
    unfold interior
    simp [List.length_dropLast, hlen]
    omega
  rw [hint_eq] at hlen'
  simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append] at hsum
  rw [← hlen']
  omega

/-! ## The action on sequences -/

end MooreFoelner.Dev.Delta

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Delta

end MooreFoelner
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Delta in
theorem solution (T : Finset Seq) (hT : IsTree T) :
    (2 : ℝ) ^ (((delta T).card : ℤ) - 2) < T.card := by
  have hTpos : (1 : ℝ) ≤ T.card := by
    have := Finset.card_pos.2 (tr_nonempty hT)
    exact_mod_cast this
  have small : ∀ n : ℕ, n ≤ 1 → (2 : ℝ) ^ ((n : ℤ) - 2) < T.card := by
    intro n hn
    have : (2 : ℝ) ^ ((n : ℤ) - 2) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
    rw [h2] at this
    linarith
  by_cases h : ∃ U, IsTree U ∧ Dominated U T ∧ DeltaConditions T U ∧
      ∀ V, IsTree V → Dominated V T → DeltaConditions T V → Dominated V U
  · rw [delta, dif_pos h]
    obtain ⟨hU, hUT, hD, -⟩ := Classical.choose_spec h
    rcases le_or_gt (Classical.choose h).card 1 with hn | hn
    · exact small _ hn
    · have key := card_bound hU hUT hD.2.2.1 hn
      have : (((Classical.choose h).card : ℤ) - 2) = (((Classical.choose h).card - 2 : ℕ) : ℤ) := by
        omega
      rw [this, zpow_natCast]
      exact_mod_cast key
  · rw [delta, dif_neg h]
    exact small 1 le_rfl |>.trans_eq' (by simp [trivialTree])
