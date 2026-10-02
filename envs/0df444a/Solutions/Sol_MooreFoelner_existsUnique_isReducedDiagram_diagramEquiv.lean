-- Prove2me | solution 1 for MooreFoelner.existsUnique_isReducedDiagram_diagramEquiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T03:10:49.702889+00:00
-- url     : https://prove2.me/submissions/470aa421-f3bf-49c6-9fda-61b8cc8913ef

import Theorems.Thm_MooreFoelner_isReducedDiagram_iff
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
# Moore 2013, §2: reduced tree diagrams (targets #3, #4, #5)

#3 and #4 are proved combinatorially on sequences: a common caret can be removed (`reduce_step`),
and a diagram with no common caret is refined by every equivalent diagram
(`refine_of_not_commonCaret`). For #5, a diagram describes `f` iff `f (0.x) = 0.(x·D)` for every
infinite sequence `x` (`describes_iff`); maps that locally replace prefixes are determined by
their real values (`eq_of_locPR`); and CFP's `exists_represents` / `exists_isReduced_represents`
are transported through `addrs`, the leaf addresses of a CFP tree.
-/

namespace MooreFoelner.Dev.Diagrams

open MooreFoelner CannonFloydParry Classical

/-! ### Infinite sequences with a finite prefix -/

/-- `u⁀y`: the finite sequence `u` followed by the infinite sequence `y`. -/
def app (u : Seq) (y : ℕ → Bool) : ℕ → Bool :=
  fun n => if h : n < u.length then u[n] else y (n - u.length)

/-- The infinite sequence `x` with its first `k` digits removed. -/
def shift (x : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun n => x (n + k)

@[simp] lemma app_nil (y : ℕ → Bool) : app [] y = y := by
  funext n; simp [app]

lemma app_append (u v : Seq) (y : ℕ → Bool) : app (u ++ v) y = app u (app v y) := by
  funext n
  simp only [app, List.length_append]
  by_cases h1 : n < u.length
  · rw [dif_pos (by omega), dif_pos h1, List.getElem_append_left h1]
  · rw [dif_neg h1]
    by_cases h2 : n < u.length + v.length
    · rw [dif_pos h2, dif_pos (by omega), List.getElem_append_right (by omega)]
    · rw [dif_neg h2, dif_neg (by omega)]
      congr 1; omega

lemma isInitialPart_app (u : Seq) (y : ℕ → Bool) : IsInitialPart u (app u y) := by
  intro i h
  simp [app, h]

lemma shift_app (u : Seq) (y : ℕ → Bool) : shift (app u y) u.length = y := by
  funext n; simp [shift, app]

lemma app_shift {u : Seq} {x : ℕ → Bool} (h : IsInitialPart u x) : app u (shift x u.length) = x := by
  funext n
  simp only [app, shift]
  split_ifs with hn
  · exact h n hn
  · congr 1; omega

lemma isInitialPart_iff_exists {u : Seq} {x : ℕ → Bool} :
    IsInitialPart u x ↔ ∃ y, x = app u y :=
  ⟨fun h => ⟨_, (app_shift h).symm⟩, fun ⟨y, hy⟩ => hy ▸ isInitialPart_app u y⟩

lemma prefix_of_isInitialPart {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) (hl : u.length ≤ v.length) : u <+: v := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have e1 := hu i h1
  have e2 := hv i (by omega)
  simp only [List.get_eq_getElem] at e1 e2
  rw [List.getElem_take, e1, e2]

lemma comparable_of_isInitialPart {u v : Seq} {x : ℕ → Bool} (hu : IsInitialPart u x)
    (hv : IsInitialPart v x) : u <+: v ∨ v <+: u := by
  rcases le_total u.length v.length with h | h
  · exact Or.inl (prefix_of_isInitialPart hu hv h)
  · exact Or.inr (prefix_of_isInitialPart hv hu h)

lemma isInitialPart_of_prefix {u v : Seq} {x : ℕ → Bool} (hv : IsInitialPart v x)
    (h : u <+: v) : IsInitialPart u x := by
  obtain ⟨w, rfl⟩ := h
  intro i hi
  have e := hv i (by simp; omega)
  simp only [List.get_eq_getElem] at e ⊢
  rw [← e, List.getElem_append_left hi]

lemma isInitialPart_append_app {u w : Seq} {y : ℕ → Bool} :
    IsInitialPart (u ++ w) (app u y) ↔ IsInitialPart w y := by
  constructor
  · intro h i hi
    have := h (u.length + i) (by simp; omega)
    simp only [List.get_eq_getElem] at this ⊢
    rw [List.getElem_append_right (by omega)] at this
    simp only [Nat.add_sub_cancel_left] at this
    rw [this]; simp [app]
  · intro h
    rw [isInitialPart_iff_exists] at h ⊢
    obtain ⟨z, rfl⟩ := h
    exact ⟨z, by rw [app_append]⟩

lemma app_inj_left {u v : Seq} (h : ∀ y, app u y = app v y) : u = v := by
  have key : ∀ u v : Seq, (∀ y, app u y = app v y) → u.length ≤ v.length → u = v := by
    intro u v h hl
    have hp : u <+: v := prefix_of_isInitialPart (x := app u (fun _ => false))
      (isInitialPart_app _ _) (by rw [h]; exact isInitialPart_app _ _) hl
    obtain ⟨w, rfl⟩ := hp
    cases w with
    | nil => simp
    | cons c w =>
      exfalso
      have := h (fun _ => !c)
      rw [app_append] at this
      have h2 := congrArg (fun z => shift z u.length) this
      simp only [shift_app] at h2
      have h3 := congrFun h2 0
      simp [app] at h3
  rcases le_total u.length v.length with hl | hl
  · exact key u v h hl
  · exact (key v u (fun y => (h y).symm) hl).symm

/-! ### The lexicographic order -/

/-- Neither of `u`, `v` is an initial part of the other. -/
def Incomp (u v : Seq) : Prop := ¬ u <+: v ∧ ¬ v <+: u

lemma Incomp.symm {u v : Seq} (h : Incomp u v) : Incomp v u := ⟨h.2, h.1⟩

lemma append_lt_append_of_incomp : ∀ {u v : Seq}, Incomp u v → u < v → ∀ a b : Seq, u ++ a < v ++ b
  | [], v, h, _, _, _ => absurd (List.nil_prefix) h.1
  | _ :: _, [], h, _, _, _ => absurd (List.nil_prefix) h.2
  | c :: u, d :: v, h, hlt, a, b => by
    change List.Lex (· < ·) (c :: u) (d :: v) at hlt
    change List.Lex (· < ·) (c :: (u ++ a)) (d :: (v ++ b))
    cases hlt with
    | cons hlt =>
      have hi : Incomp u v := ⟨fun hp => h.1 (List.prefix_cons_inj c |>.mpr hp),
        fun hp => h.2 (List.prefix_cons_inj c |>.mpr hp)⟩
      exact List.Lex.cons (append_lt_append_of_incomp hi hlt a b)
    | rel hcd => exact List.Lex.rel hcd

lemma append_false_lt_append_true (u a b : Seq) : u ++ false :: a < u ++ true :: b := by
  show List.Lex (· < ·) (u ++ false :: a) (u ++ true :: b)
  exact List.Lex.append_left _ (List.Lex.rel (by decide)) u

/-! ### Merge sort with a strict comparison on a list without duplicates -/

lemma merge_congr {α : Type*} {r s : α → α → Bool} :
    ∀ (xs ys : List α), (∀ a ∈ xs, ∀ b ∈ ys, r a b = s a b) → xs.merge ys r = xs.merge ys s
  | [], ys, _ => by simp
  | x :: xs, [], _ => by simp
  | x :: xs, y :: ys, h => by
    rw [List.cons_merge_cons, List.cons_merge_cons, h x (by simp) y (by simp)]
    split
    · rw [merge_congr xs (y :: ys) (fun a ha b hb => h a (by simp [ha]) b hb)]
    · rw [merge_congr (x :: xs) ys (fun a ha b hb => h a ha b (by simp [hb]))]

lemma mergeSort_congr {α : Type*} {r s : α → α → Bool} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b = s a b) →
      l.mergeSort r = l.mergeSort s
  | [], _, _ => by simp
  | [x], _, _ => by simp
  | a :: b :: l, hnd, hl => by
    simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd]
    set k := ((a :: b :: l).length + 1) / 2
    have hdisj : ∀ x ∈ (a :: b :: l).take k, ∀ y ∈ (a :: b :: l).drop k, x ≠ y := by
      have := List.take_append_drop k (a :: b :: l)
      rw [← this] at hnd
      have hd := List.disjoint_of_nodup_append hnd
      intro x hx y hy hxy
      subst hxy
      exact hd hx hy
    have h1 : ((a :: b :: l).take k).length < (a :: b :: l).length := by
      simp only [List.length_take, List.length_cons, k]; omega
    have h2 : ((a :: b :: l).drop k).length < (a :: b :: l).length := by
      simp only [List.length_drop, List.length_cons, k]; omega
    rw [mergeSort_congr (hnd.sublist (List.take_sublist _ _))
        (fun x hx y hy hxy => hl x (List.mem_of_mem_take hx) y (List.mem_of_mem_take hy) hxy),
      mergeSort_congr (hnd.sublist (List.drop_sublist _ _))
        (fun x hx y hy hxy => hl x (List.mem_of_mem_drop hx) y (List.mem_of_mem_drop hy) hxy)]
    apply merge_congr
    intro x hx y hy
    rw [List.mem_mergeSort] at hx hy
    exact hl x (List.mem_of_mem_take hx) y (List.mem_of_mem_drop hy) (hdisj x hx y hy)
  termination_by l => l.length

/-! ### `sorted` -/

lemma sorted_eq_mergeSort_le (T : Finset Seq) :
    sorted T = T.toList.mergeSort (fun u v => decide (u ≤ v)) := by
  unfold sorted
  apply mergeSort_congr (Finset.nodup_toList T)
  intro a _ b _ hab
  rw [decide_eq_decide]
  exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h hab⟩

lemma mem_sorted {T : Finset Seq} {u : Seq} : u ∈ sorted T ↔ u ∈ T := by
  simp [sorted]

lemma length_sorted (T : Finset Seq) : (sorted T).length = T.card := by
  simp [sorted]

lemma sorted_nodup (T : Finset Seq) : (sorted T).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList T)

lemma sorted_pairwise (T : Finset Seq) : (sorted T).Pairwise (· < ·) := by
  have h1 : (sorted T).Pairwise (fun u v => decide (u ≤ v) = true) := by
    rw [sorted_eq_mergeSort_le]
    apply List.pairwise_mergeSort
    · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc
    · intro a b; simpa using le_total a b
  have h2 := (sorted_nodup T)
  rw [List.Nodup] at h2
  refine (h1.and h2).imp ?_
  intro a b ⟨hab, hne⟩
  simp only [decide_eq_true_eq] at hab
  exact lt_of_le_of_ne hab hne

lemma toFinset_sorted (T : Finset Seq) : (sorted T).toFinset = T := by
  ext u; simp [mem_sorted]

lemma sorted_getElem_mem (T : Finset Seq) (i : ℕ) (h : i < (sorted T).length) :
    (sorted T)[i] ∈ T := mem_sorted.mp (List.getElem_mem h)

lemma sorted_lt_iff {T : Finset Seq} {i j : ℕ} (hi : i < (sorted T).length)
    (hj : j < (sorted T).length) : (sorted T)[i] < (sorted T)[j] ↔ i < j := by
  have hs : (sorted T).SortedLT := (sorted_pairwise T).sortedLT
  exact hs.strictMono_get.lt_iff_lt (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)

lemma sorted_le_iff {T : Finset Seq} {i j : ℕ} (hi : i < (sorted T).length)
    (hj : j < (sorted T).length) : (sorted T)[i] ≤ (sorted T)[j] ↔ i ≤ j := by
  have hs : (sorted T).SortedLT := (sorted_pairwise T).sortedLT
  exact hs.strictMono_get.le_iff_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩)

lemma sorted_inj {T : Finset Seq} {i j : ℕ} (hi : i < (sorted T).length)
    (hj : j < (sorted T).length) (h : (sorted T)[i] = (sorted T)[j]) : i = j := by
  apply le_antisymm
  · exact (sorted_le_iff hi hj).mp h.le
  · exact (sorted_le_iff hj hi).mp h.ge

lemma exists_sorted_eq {T : Finset Seq} {u : Seq} (hu : u ∈ T) :
    ∃ i, ∃ h : i < (sorted T).length, (sorted T)[i] = u :=
  List.getElem_of_mem (mem_sorted.mpr hu)

/-! ### Trees -/

lemma tree_exists_mem {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := (hT x).exists

lemma tree_eq_of_isInitialPart {T : Finset Seq} (hT : IsTree T) {t t' : Seq} {x : ℕ → Bool}
    (ht : t ∈ T) (ht' : t' ∈ T) (h : IsInitialPart t x) (h' : IsInitialPart t' x) : t = t' :=
  (hT x).unique ⟨ht, h⟩ ⟨ht', h'⟩

lemma tree_eq_of_prefix {T : Finset Seq} (hT : IsTree T) {u v : Seq} (hu : u ∈ T) (hv : v ∈ T)
    (h : u <+: v) : u = v :=
  tree_eq_of_isInitialPart hT hu hv (isInitialPart_of_prefix (isInitialPart_app v (fun _ => false)) h)
    (isInitialPart_app v _)

lemma tree_exists_comparable {T : Finset Seq} (hT : IsTree T) (u : Seq) :
    ∃ t ∈ T, t <+: u ∨ u <+: t := by
  obtain ⟨t, ht, h⟩ := tree_exists_mem hT (app u (fun _ => false))
  exact ⟨t, ht, comparable_of_isInitialPart h (isInitialPart_app _ _)⟩

lemma tree_sibling {T : Finset Seq} (hT : IsTree T) {u : Seq} {b : Bool} {t : Seq} (ht : t ∈ T)
    (hut : u ++ [b] <+: t) : ∃ t' ∈ T, u ++ [!b] <+: t' := by
  obtain ⟨t', ht', h⟩ := tree_exists_comparable hT (u ++ [!b])
  rcases h with h | h
  · rcases List.prefix_concat_iff.mp h with h | h
    · exact ⟨t', ht', h ▸ List.prefix_refl _⟩
    · exfalso
      have h1 : t' <+: t := h.trans ((List.prefix_append u [b]).trans hut)
      have := tree_eq_of_prefix hT ht' ht h1
      subst this
      have := h.length_le
      have := hut.length_le
      simp at this
      omega
  · exact ⟨t', ht', h⟩

/-! ### The map of a tree diagram on infinite sequences -/

lemma diagramMap_getElem {L : Finset Seq} (R : Finset Seq) (hL : IsTree L) (i : ℕ)
    (hi : i < (sorted L).length) (hi' : i < (sorted R).length) (y : ℕ → Bool) :
    diagramMap L R (app (sorted L)[i] y) = app (sorted R)[i] y := by
  have hfind : (List.finRange (sorted L).length).find?
      (fun j => decide (IsInitialPart ((sorted L).get j) (app (sorted L)[i] y))) = some ⟨i, hi⟩ := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using isInitialPart_app _ _, i, by simpa using hi, by simp, ?_⟩
    intro j hj
    simp only [List.getElem_finRange, Fin.cast_mk, List.get_eq_getElem, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    intro h
    have hj' : j < (sorted L).length := by omega
    have := tree_eq_of_isInitialPart hL (sorted_getElem_mem L j hj') (sorted_getElem_mem L i hi) h
      (isInitialPart_app _ _)
    have := sorted_inj hj' hi this
    omega
  unfold diagramMap
  simp only
  rw [hfind]
  simp only [List.get_eq_getElem, List.getElem?_eq_getElem hi']
  funext n
  simp only [app]
  split_ifs with h1 h2
  · rfl
  · omega
  · congr 1; omega

/-! ### Consecutive leaves -/

lemma append_lt_append_left_iff (u : Seq) {a b : Seq} : u ++ a < u ++ b ↔ a < b := by
  induction u with
  | nil => simp
  | cons c u ih =>
    rw [← ih]
    change List.Lex (· < ·) (c :: (u ++ a)) (c :: (u ++ b)) ↔ List.Lex (· < ·) (u ++ a) (u ++ b)
    constructor
    · intro h
      cases h with
      | cons h => exact h
      | rel h => exact absurd h (lt_irrefl c)
    · exact List.Lex.cons

lemma prefix_replicate_of_lt : ∀ {a : Seq} {k : ℕ}, a < List.replicate k false →
    a <+: List.replicate k false
  | [], _, _ => List.nil_prefix
  | c :: a, 0, h => by
    change List.Lex (· < ·) (c :: a) [] at h
    cases h
  | c :: a, k + 1, h => by
    change List.Lex (· < ·) (c :: a) (false :: List.replicate k false) at h
    cases h with
    | cons h =>
      rw [List.replicate_succ]
      exact (List.prefix_cons_inj false).mpr (prefix_replicate_of_lt h)
    | rel h => exact absurd h (by cases c <;> simp)

lemma eq_replicate_of_isInitialPart {r : Seq} (h : IsInitialPart r (fun _ => false)) :
    r = List.replicate r.length false := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have := h i h1
  simp only [List.get_eq_getElem] at this
  simp [this]

lemma prefix_antisymm {u v : Seq} (h1 : u <+: v) (h2 : v <+: u) : u = v :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

/-- In a tree, the leaf after `u0` in `<_lex` order is `u10…0`. -/
lemma tree_succ {T : Finset Seq} (hT : IsTree T) {i : ℕ} (hi : i < (sorted T).length) {u : Seq}
    (hu : (sorted T)[i] = u ++ [false]) :
    ∃ (h : i + 1 < (sorted T).length) (k : ℕ),
      (sorted T)[i + 1] = u ++ true :: List.replicate k false := by
  have hu0 : u ++ [false] ∈ T := hu ▸ sorted_getElem_mem T i hi
  set x := app (u ++ [true]) (fun _ => false) with hx
  obtain ⟨w, hw, hwx⟩ := tree_exists_mem hT x
  have hux : IsInitialPart (u ++ [true]) x := isInitialPart_app _ _
  have hlen : u.length + 1 ≤ w.length := by
    by_contra hcon
    have h1 : w <+: u ++ [true] := prefix_of_isInitialPart hwx hux (by simp; omega)
    rcases List.prefix_concat_iff.mp h1 with h1 | h1
    · simp [h1] at hcon
    · have := tree_eq_of_prefix hT hw hu0 (h1.trans (List.prefix_append u [false]))
      subst this; simp at hcon
  have h2 : u ++ [true] <+: w := prefix_of_isInitialPart hux hwx (by simp; omega)
  obtain ⟨r, rfl⟩ := h2
  have hr : IsInitialPart r (fun _ => false) := by
    rw [hx] at hwx
    exact isInitialPart_append_app.mp hwx
  rw [eq_replicate_of_isInitialPart hr] at hw
  set k := r.length
  have hw' : u ++ true :: List.replicate k false ∈ T := by simpa using hw
  obtain ⟨j, hj, hjw⟩ := exists_sorted_eq hw'
  have hij : i < j := by
    rw [← sorted_lt_iff hi hj, hu, hjw]
    exact append_false_lt_append_true _ _ _
  have hi1 : i + 1 < (sorted T).length := by omega
  refine ⟨hi1, k, ?_⟩
  set z := (sorted T)[i + 1] with hz
  have hzT : z ∈ T := sorted_getElem_mem T _ hi1
  have hz1 : u ++ [false] < z := by rw [← hu, hz, sorted_lt_iff]; omega
  have hz2 : z ≤ u ++ true :: List.replicate k false := by
    rw [← hjw, hz, sorted_le_iff]; omega
  rcases hz2.lt_or_eq with hz2 | hz2
  · exfalso
    by_cases hc1 : z <+: u
    · have := tree_eq_of_prefix hT hzT hu0 (hc1.trans (List.prefix_append u [false]))
      rw [this] at hz1; exact lt_irrefl _ hz1
    by_cases hc2 : u <+: z
    · obtain ⟨r', hr'⟩ := hc2
      rcases r' with _ | ⟨c, r''⟩
      · simp at hr'; exact hc1 (hr' ▸ List.prefix_refl u)
      · cases c
        · have := tree_eq_of_prefix hT hu0 hzT (by rw [← hr']; simp)
          rw [← this] at hz1; exact lt_irrefl _ hz1
        · rw [← hr'] at hz2
          have h3 := (append_lt_append_left_iff (u ++ [true])).mp (by simpa using hz2)
          have h4 := prefix_replicate_of_lt h3
          have h5 : z <+: u ++ true :: List.replicate k false := by
            rw [← hr']; simpa using h4
          have := tree_eq_of_prefix hT hzT hw' h5
          rw [hr', this] at hz2; exact lt_irrefl _ hz2
    · have hinc : Incomp z u := ⟨hc1, hc2⟩
      rcases lt_trichotomy z u with h3 | h3 | h3
      · have := append_lt_append_of_incomp hinc h3 [] [false]
        simp at this
        exact lt_irrefl _ (hz1.trans this)
      · exact hc1 (h3 ▸ List.prefix_refl u)
      · have := append_lt_append_of_incomp hinc.symm h3 (true :: List.replicate k false) []
        simp at this
        exact lt_irrefl _ (hz2.trans this)
  · exact hz2

lemma tree_sibling_consecutive {T : Finset Seq} (hT : IsTree T) {u : Seq} (h0 : u ++ [false] ∈ T)
    (h1 : u ++ [true] ∈ T) : ∃ i, ∃ h : i + 1 < (sorted T).length,
      (sorted T)[i] = u ++ [false] ∧ (sorted T)[i + 1] = u ++ [true] := by
  obtain ⟨i, hi, hu⟩ := exists_sorted_eq h0
  obtain ⟨h, k, hk⟩ := tree_succ hT hi hu
  refine ⟨i, h, hu, ?_⟩
  rw [hk]
  have := tree_eq_of_prefix hT h1 (hk ▸ sorted_getElem_mem T (i + 1) h) (by simp)
  rw [← this]

/-! ### Removing a caret -/

/-! ### Diagrams without a common caret -/

/-- The right side of #4: a common caret at some position. -/
def CommonCaret (S T : Finset Seq) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < (sorted S).length) (hi' : i + 1 < (sorted T).length),
    ((sorted S).get ⟨i, by omega⟩).getLast? = some false ∧
    ((sorted T).get ⟨i, by omega⟩).getLast? = some false ∧
    ((sorted S).get ⟨i + 1, hi⟩).getLast? = some true ∧
    ((sorted T).get ⟨i + 1, hi'⟩).getLast? = some true

lemma refine_of_not_commonCaret {L R L' R' : Finset Seq} (h : IsTreeDiagram L R)
    (hnc : ¬ CommonCaret L R) (h' : IsTreeDiagram L' R') (he : DiagramEquiv L R L' R') :
    ∀ s' ∈ L', ∃ s ∈ L, s <+: s' := by
  intro s' hs'
  by_contra hcon
  push Not at hcon
  set A := L.filter (fun t => s' <+: t) with hAdef
  have hA : A.Nonempty := by
    obtain ⟨t, ht, h1 | h1⟩ := tree_exists_comparable h.1 s'
    · exact absurd h1 (hcon t ht)
    · exact ⟨t, Finset.mem_filter.mpr ⟨ht, h1⟩⟩
  obtain ⟨a, haA, hmax⟩ := Finset.exists_max_image A List.length hA
  obtain ⟨haL, r, rfl⟩ := Finset.mem_filter.mp haA
  rcases List.eq_nil_or_concat r with rfl | ⟨c, b, rfl⟩
  · exact hcon _ haL (by simp)
  set U := s' ++ c with hU
  have haU : s' ++ c.concat b = U ++ [b] := by simp [U]
  rw [haU] at haL hmax
  obtain ⟨t', ht', hpre⟩ := tree_sibling h.1 haL (List.prefix_refl _)
  have ht'A : t' ∈ A := Finset.mem_filter.mpr ⟨ht', (List.prefix_append s' (c ++ [!b])).trans
    (by simpa [U] using hpre)⟩
  have hlen := hmax t' ht'A
  have heq : U ++ [!b] = t' := hpre.eq_of_length (by
    have := hpre.length_le; simp at hlen this ⊢; omega)
  have hb : U ++ [false] ∈ L ∧ U ++ [true] ∈ L := by
    cases b
    · exact ⟨haL, by rw [← heq] at ht'; simpa using ht'⟩
    · exact ⟨by rw [← heq] at ht'; simpa using ht', haL⟩
  obtain ⟨i, hi, e0, e1⟩ := tree_sibling_consecutive h.1 hb.1 hb.2
  obtain ⟨j, hj, rfl⟩ := exists_sorted_eq hs'
  have hj' : j < (sorted R').length := by
    rw [length_sorted] at hj ⊢; have := h'.2.2; omega
  have hi' : i + 1 < (sorted R).length := by
    rw [length_sorted] at hi ⊢; have := h.2.2; omega
  have key : ∀ (k : ℕ) (hk : k < (sorted L).length) (hk' : k < (sorted R).length) (b' : Bool),
      (sorted L)[k] = U ++ [b'] → (sorted R)[k] = (sorted R')[j] ++ c ++ [b'] := by
    intro k hk hk' b' hkb
    apply app_inj_left
    intro y
    rw [← diagramMap_getElem R h.1 k hk hk' y, he, hkb,
      show U ++ [b'] = (sorted L')[j] ++ (c ++ [b']) by simp [U], app_append,
      diagramMap_getElem R' h'.1 j hj hj', ← app_append, List.append_assoc]
  have k0 := key i (by omega) (by omega) false e0
  have k1 := key (i + 1) hi hi' true e1
  apply hnc
  refine ⟨i, hi, hi', ?_, ?_, ?_, ?_⟩ <;> simp only [List.get_eq_getElem]
  · rw [e0]; simp
  · rw [k0]; simp
  · rw [e1]; simp
  · rw [k1]; simp

lemma eq_of_refine {L L' : Finset Seq} (hL : IsTree L) (hL' : IsTree L')
    (h1 : ∀ s' ∈ L', ∃ s ∈ L, s <+: s') (h2 : ∀ s ∈ L, ∃ s' ∈ L', s' <+: s) : L = L' := by
  have half : ∀ {A B : Finset Seq}, IsTree A → (∀ s' ∈ B, ∃ s ∈ A, s <+: s') →
      (∀ s ∈ A, ∃ s' ∈ B, s' <+: s) → ∀ a ∈ A, a ∈ B := by
    intro A B hA h1 h2 a ha
    obtain ⟨s', hs', h3⟩ := h2 a ha
    obtain ⟨s, hs, h4⟩ := h1 s' hs'
    have e1 : s = a := tree_eq_of_prefix hA hs ha (h4.trans h3)
    have e2 : s' = a := prefix_antisymm h3 (e1 ▸ h4)
    exact e2 ▸ hs'
  ext a
  exact ⟨half hL h1 h2 a, half hL' h2 h1 a⟩

lemma reduced_iff {S T : Finset Seq} (h : IsTreeDiagram S T) :
    IsReducedDiagram S T ↔ ¬ CommonCaret S T :=
  MooreFoelner.isReducedDiagram_iff S T h

lemma diagramEquiv_symm {L R L' R' : Finset Seq} (h : DiagramEquiv L R L' R') :
    DiagramEquiv L' R' L R := fun x => (h x).symm

lemma diagramEquiv_trans {L R L' R' L'' R'' : Finset Seq} (h : DiagramEquiv L R L' R')
    (h' : DiagramEquiv L' R' L'' R'') : DiagramEquiv L R L'' R'' := fun x => (h x).trans (h' x)

lemma reduced_unique {L R L' R' : Finset Seq} (h1 : IsReducedDiagram L R)
    (h2 : IsReducedDiagram L' R') (he : DiagramEquiv L R L' R') : L = L' ∧ R = R' := by
  have nc1 := (reduced_iff h1.1).mp h1
  have nc2 := (reduced_iff h2.1).mp h2
  have hLL : L = L' := eq_of_refine h1.1.1 h2.1.1 (refine_of_not_commonCaret h1.1 nc1 h2.1 he)
    (refine_of_not_commonCaret h2.1 nc2 h1.1 (diagramEquiv_symm he))
  subst hLL
  refine ⟨rfl, ?_⟩
  rw [← toFinset_sorted R, ← toFinset_sorted R']
  congr 1
  have c1 := h1.1.2.2
  have c2 := h2.1.2.2
  have hlen : (sorted R).length = (sorted R').length := by simp only [length_sorted]; omega
  apply List.ext_getElem hlen
  intro n hn hn'
  have hnL : n < (sorted L).length := by rw [length_sorted] at hn ⊢; omega
  apply app_inj_left; intro y
  rw [← diagramMap_getElem R h1.1.1 n hnL hn y, he, diagramMap_getElem R' h1.1.1 n hnL hn' y]

lemma exists_reduced_equiv {L R : Finset Seq} (h : IsTreeDiagram L R) :
    ∃ L' R', IsReducedDiagram L' R' ∧ DiagramEquiv L R L' R' := by
  have hP : ∃ n, ∃ L' R', IsTreeDiagram L' R' ∧ DiagramEquiv L R L' R' ∧ L'.card = n :=
    ⟨_, L, R, h, fun _ => rfl, rfl⟩
  obtain ⟨L', R', h', he, hn⟩ := Nat.find_spec hP
  refine ⟨L', R', ⟨h', fun L'' R'' h'' he' => ?_⟩, he⟩
  rw [hn]
  exact Nat.find_min' hP ⟨L'', R'', h'', diagramEquiv_trans he he', rfl⟩

end MooreFoelner.Dev.Diagrams

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner

namespace MooreFoelner.Dev.Diagrams

open MooreFoelner CannonFloydParry Classical

/-! ### Binary expansions -/

/-! ### `Describes` and the map on infinite sequences -/

/-! ### Maps that are locally prefix replacements -/

/-! ### Consequences for diagrams describing maps -/

/-! ### Cannon–Floyd–Parry's trees as sets of leaf addresses -/

/-- `T/b`: the subtree below the digit `b`. -/
def part (T : Finset Seq) (b : Bool) : Finset Seq :=
  (T.filter (fun u => u.head? = some b)).image List.tail

/-! ### `marks` and `seqVal` -/

/-! ### Reduced diagrams and Thompson's group -/

end MooreFoelner.Dev.Diagrams

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open MooreFoelner CannonFloydParry Classical in
open Classical CannonFloydParry in
theorem solution (L R : Finset Seq) (h : IsTreeDiagram L R) :
    ∃! D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 ∧ DiagramEquiv L R D.1 D.2 := by
  obtain ⟨L', R', hr, he⟩ := Dev.Diagrams.exists_reduced_equiv h
  refine ⟨(L', R'), ⟨hr, he⟩, ?_⟩
  rintro ⟨L'', R''⟩ ⟨hr', he'⟩
  obtain ⟨e1, e2⟩ := Dev.Diagrams.reduced_unique hr' hr
    (Dev.Diagrams.diagramEquiv_trans (Dev.Diagrams.diagramEquiv_symm he') he)
  exact Prod.ext e1 e2
