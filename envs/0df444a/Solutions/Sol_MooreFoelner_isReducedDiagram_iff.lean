-- Prove2me | solution 1 for MooreFoelner.isReducedDiagram_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T03:26:41.783626+00:00
-- url     : https://prove2.me/submissions/6ee92117-00ea-40f0-8103-46b7db6e2c05

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

lemma sorted_eq_of {T : Finset Seq} {l : List Seq} (hl : l.Pairwise (· < ·))
    (hmem : ∀ a, a ∈ l ↔ a ∈ T) : sorted T = l :=
  List.Pairwise.eq_of_mem_iff (sorted_pairwise T) hl (fun a => by rw [mem_sorted, hmem])

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

lemma tree_eq_of_comparable {T : Finset Seq} (hT : IsTree T) {u v : Seq} (hu : u ∈ T)
    (hv : v ∈ T) (h : u <+: v ∨ v <+: u) : u = v := by
  rcases h with h | h
  · exact tree_eq_of_prefix hT hu hv h
  · exact (tree_eq_of_prefix hT hv hu h).symm

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

lemma diagramMap_eq_app {L : Finset Seq} (R : Finset Seq) (hL : IsTree L) (hc : L.card = R.card)
    (x : ℕ → Bool) : ∃ i, ∃ (hi : i < (sorted L).length) (hi' : i < (sorted R).length) (y : ℕ → Bool),
      x = app (sorted L)[i] y ∧ diagramMap L R x = app (sorted R)[i] y := by
  obtain ⟨t, ht, hx⟩ := tree_exists_mem hL x
  obtain ⟨i, hi, rfl⟩ := exists_sorted_eq ht
  have hi' : i < (sorted R).length := by rw [length_sorted] at hi ⊢; omega
  obtain ⟨y, rfl⟩ := isInitialPart_iff_exists.mp hx
  exact ⟨i, hi, hi', y, rfl, diagramMap_getElem R hL i hi hi' y⟩

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

lemma not_mem_of_append_mem {T : Finset Seq} (hT : IsTree T) {u : Seq} {b : Bool}
    (h : u ++ [b] ∈ T) : u ∉ T := by
  intro hu
  have := tree_eq_of_prefix hT hu h (List.prefix_append u [b])
  have := congrArg List.length this
  simp at this

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

lemma tree_consecutive {T : Finset Seq} (hT : IsTree T) {i : ℕ} (h : i + 1 < (sorted T).length)
    (h0 : ((sorted T)[i]).getLast? = some false) (h1 : ((sorted T)[i + 1]).getLast? = some true) :
    ∃ u, (sorted T)[i] = u ++ [false] ∧ (sorted T)[i + 1] = u ++ [true] := by
  obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp h0
  obtain ⟨_, k, hk⟩ := tree_succ hT (by omega) hu
  refine ⟨u, hu, ?_⟩
  rw [hk] at h1 ⊢
  cases k with
  | zero => simp
  | succ k =>
    rw [List.replicate_succ'] at h1
    have e : u ++ true :: (List.replicate k false ++ [false]) =
      (u ++ true :: List.replicate k false) ++ [false] := by simp
    rw [e, List.getLast?_concat] at h1
    simp at h1

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

/-- `T` with the sibling leaves `u0`, `u1` replaced by `u`. -/
noncomputable def collapse (T : Finset Seq) (u : Seq) : Finset Seq :=
  insert u ((T.erase (u ++ [false])).erase (u ++ [true]))

lemma mem_collapse {T : Finset Seq} {u a : Seq} :
    a ∈ collapse T u ↔ a = u ∨ (a ∈ T ∧ a ≠ u ++ [false] ∧ a ≠ u ++ [true]) := by
  simp only [collapse, Finset.mem_insert, Finset.mem_erase]
  tauto

lemma incomp_of_ne_sibling {T : Finset Seq} (hT : IsTree T) {u a : Seq} (h0 : u ++ [false] ∈ T)
    (h1 : u ++ [true] ∈ T) (ha : a ∈ T) (ha0 : a ≠ u ++ [false]) (ha1 : a ≠ u ++ [true]) :
    Incomp a u := by
  constructor
  · intro h
    exact ha0 (tree_eq_of_prefix hT ha h0 (h.trans (List.prefix_append _ _)))
  · rintro ⟨r, rfl⟩
    rcases r with _ | ⟨c, r⟩
    · exact not_mem_of_append_mem hT h0 (by simpa using ha)
    · cases c
      · exact ha0 (tree_eq_of_prefix hT h0 ha (by simp)).symm
      · exact ha1 (tree_eq_of_prefix hT h1 ha (by simp)).symm

lemma isTree_collapse {T : Finset Seq} (hT : IsTree T) {u : Seq} (h0 : u ++ [false] ∈ T)
    (h1 : u ++ [true] ∈ T) : IsTree (collapse T u) := by
  intro x
  have key : ∀ a ∈ collapse T u, IsInitialPart a x → IsInitialPart u x → a = u := by
    intro a ha hax hux
    rcases mem_collapse.mp ha with ha | ⟨ha, ha0, ha1⟩
    · exact ha
    exfalso
    have hinc := incomp_of_ne_sibling hT h0 h1 ha ha0 ha1
    rcases comparable_of_isInitialPart hax hux with h | h
    · exact hinc.1 h
    · exact hinc.2 h
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨t, ht, htx⟩ := tree_exists_mem hT x
    by_cases ht0 : t = u ++ [false]
    · exact ⟨u, mem_collapse.mpr (Or.inl rfl),
        isInitialPart_of_prefix htx (ht0 ▸ List.prefix_append _ _)⟩
    by_cases ht1 : t = u ++ [true]
    · exact ⟨u, mem_collapse.mpr (Or.inl rfl),
        isInitialPart_of_prefix htx (ht1 ▸ List.prefix_append _ _)⟩
    exact ⟨t, mem_collapse.mpr (Or.inr ⟨ht, ht0, ht1⟩), htx⟩
  · rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    by_cases hux : IsInitialPart u x
    · rw [key a ha hax hux, key b hb hbx hux]
    · have ha' : a ∈ T := by
        rcases mem_collapse.mp ha with rfl | ⟨ha, -⟩
        · exact absurd hax hux
        · exact ha
      have hb' : b ∈ T := by
        rcases mem_collapse.mp hb with rfl | ⟨hb, -⟩
        · exact absurd hbx hux
        · exact hb
      exact tree_eq_of_isInitialPart hT ha' hb' hax hbx

lemma card_collapse {T : Finset Seq} (hT : IsTree T) {u : Seq} (h0 : u ++ [false] ∈ T)
    (h1 : u ++ [true] ∈ T) : (collapse T u).card + 1 = T.card := by
  have hne : u ++ [true] ≠ u ++ [false] := by simp
  have hu : u ∉ (T.erase (u ++ [false])).erase (u ++ [true]) := by
    simp only [Finset.mem_erase]
    exact fun ⟨_, _, h⟩ => not_mem_of_append_mem hT h0 h
  rw [collapse, Finset.card_insert_of_notMem hu, Finset.card_erase_of_mem
    (Finset.mem_erase.mpr ⟨hne, h1⟩), Finset.card_erase_of_mem h0]
  have : 2 ≤ T.card := by
    have : ({u ++ [false], u ++ [true]} : Finset Seq) ⊆ T := by
      intro a ha; simp at ha; rcases ha with rfl | rfl <;> assumption
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hne.symm] at h2
    exact h2
  omega

lemma getElem_collapseList {α : Type*} (l : List α) (a : α) (i : ℕ) (hi : i + 1 < l.length) (j : ℕ)
    (hj : j < (l.take i ++ a :: l.drop (i + 2)).length) :
    (l.take i ++ a :: l.drop (i + 2))[j] =
      if h1 : j < i then l[j]'(by omega) else if j = i then a else l[j + 1]'(by
        simp at hj; omega) := by
  have hti : (l.take i).length = i := by simp; omega
  split_ifs with h1 h2
  · rw [List.getElem_append_left (by omega), List.getElem_take]
  · subst h2
    rw [List.getElem_append_right (by omega)]
    simp [hti]
  · rw [List.getElem_append_right (by omega)]
    have : j - (l.take i).length = (j - i - 1) + 1 := by omega
    simp only [this, List.getElem_cons_succ, List.getElem_drop]
    congr 1; omega

lemma length_collapseList {α : Type*} (l : List α) (a : α) (i : ℕ) (hi : i + 1 < l.length) :
    (l.take i ++ a :: l.drop (i + 2)).length + 1 = l.length := by
  simp; omega

lemma sorted_collapse {T : Finset Seq} (hT : IsTree T) {i : ℕ} (hi : i + 1 < (sorted T).length)
    {u : Seq} (hu0 : (sorted T)[i] = u ++ [false]) (hu1 : (sorted T)[i + 1] = u ++ [true]) :
    sorted (collapse T u) = (sorted T).take i ++ u :: (sorted T).drop (i + 2) := by
  have h0 : u ++ [false] ∈ T := hu0 ▸ sorted_getElem_mem T i (by omega)
  have h1 : u ++ [true] ∈ T := hu1 ▸ sorted_getElem_mem T (i + 1) hi
  have hP := sorted_pairwise T
  -- an element of `T` other than `u0`, `u1` is in the first or the last part
  have hpos : ∀ a, (a ∈ (sorted T).take i → a < u) ∧ (a ∈ (sorted T).drop (i + 2) → u < a) ∧
      (a ∈ (sorted T).take i ∨ a ∈ (sorted T).drop (i + 2) ↔
        a ∈ T ∧ a ≠ u ++ [false] ∧ a ≠ u ++ [true]) := by
    intro a
    have hne0 : ∀ j (hj : j < (sorted T).length), j ≠ i → (sorted T)[j] ≠ u ++ [false] := by
      intro j hj hji h
      exact hji (sorted_inj hj (by omega) (h.trans hu0.symm))
    have hne1 : ∀ j (hj : j < (sorted T).length), j ≠ i + 1 → (sorted T)[j] ≠ u ++ [true] := by
      intro j hj hji h
      exact hji (sorted_inj hj hi (h.trans hu1.symm))
    refine ⟨?_, ?_, ?_⟩
    · intro ha
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp ha
      have hj' : j < (sorted T).length := by omega
      have hinc := incomp_of_ne_sibling hT h0 h1 (sorted_getElem_mem T j hj')
        (hne0 j hj' (by omega)) (hne1 j hj' (by omega))
      have hlt : (sorted T)[j] < u ++ [false] := by
        rw [← hu0, sorted_lt_iff]; omega
      rcases lt_trichotomy (sorted T)[j] u with h | h | h
      · exact h
      · exact absurd (h ▸ List.prefix_refl _) hinc.1
      · have := append_lt_append_of_incomp hinc.symm h [false] []
        simp at this
        exact absurd (hlt.trans this) (lt_irrefl _)
    · intro ha
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp ha
      have hj2 : i + 2 + j < (sorted T).length := by omega
      have hinc := incomp_of_ne_sibling hT h0 h1 (sorted_getElem_mem T _ hj2)
        (hne0 _ hj2 (by omega)) (hne1 _ hj2 (by omega))
      have hlt : u ++ [true] < (sorted T)[i + 2 + j] := by
        rw [← hu1, sorted_lt_iff]; omega
      rcases lt_trichotomy (sorted T)[i + 2 + j] u with h | h | h
      · have := append_lt_append_of_incomp hinc h [] [true]
        simp at this
        exact absurd (hlt.trans this) (lt_irrefl _)
      · exact absurd (h ▸ List.prefix_refl _) hinc.1
      · exact h
    · constructor
      · rintro (ha | ha)
        · obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp ha
          have hj' : j < (sorted T).length := by omega
          exact ⟨sorted_getElem_mem T j hj', hne0 j hj' (by omega), hne1 j hj' (by omega)⟩
        · obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp ha
          have hj2 : i + 2 + j < (sorted T).length := by omega
          exact ⟨sorted_getElem_mem T _ hj2, hne0 _ hj2 (by omega), hne1 _ hj2 (by omega)⟩
      · rintro ⟨ha, ha0, ha1⟩
        obtain ⟨j, hj, rfl⟩ := exists_sorted_eq ha
        have hji : j ≠ i := fun h => ha0 (by subst h; exact hu0)
        have hji1 : j ≠ i + 1 := fun h => ha1 (by subst h; exact hu1)
        rcases Nat.lt_or_gt_of_ne hji with h | h
        · exact Or.inl (List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩)
        · exact Or.inr (List.mem_drop_iff_getElem.mpr ⟨j - (i + 2), by omega, by congr 1; omega⟩)
  apply sorted_eq_of
  · rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hP.sublist (List.take_sublist _ _), ⟨fun b hb => (hpos b).2.1 hb,
      hP.sublist (List.drop_sublist _ _)⟩, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (hpos a).1 ha
    · exact ((hpos a).1 ha).trans ((hpos b).2.1 hb)
  · intro a
    rw [List.mem_append, List.mem_cons, mem_collapse]
    have := (hpos a).2.2
    tauto

/-- A common caret can be removed, giving an equivalent tree diagram with fewer leaves. -/
lemma reduce_step {L R : Finset Seq} (h : IsTreeDiagram L R) {i : ℕ}
    (hi : i + 1 < (sorted L).length) (hi' : i + 1 < (sorted R).length) {u v : Seq}
    (hu0 : (sorted L)[i] = u ++ [false]) (hu1 : (sorted L)[i + 1] = u ++ [true])
    (hv0 : (sorted R)[i] = v ++ [false]) (hv1 : (sorted R)[i + 1] = v ++ [true]) :
    IsTreeDiagram (collapse L u) (collapse R v) ∧ DiagramEquiv L R (collapse L u) (collapse R v) ∧
      (collapse L u).card < L.card := by
  have hL0 : u ++ [false] ∈ L := hu0 ▸ sorted_getElem_mem L i (by omega)
  have hL1 : u ++ [true] ∈ L := hu1 ▸ sorted_getElem_mem L (i + 1) hi
  have hR0 : v ++ [false] ∈ R := hv0 ▸ sorted_getElem_mem R i (by omega)
  have hR1 : v ++ [true] ∈ R := hv1 ▸ sorted_getElem_mem R (i + 1) hi'
  have cL := card_collapse h.1 hL0 hL1
  have cR := card_collapse h.2.1 hR0 hR1
  have hTD : IsTreeDiagram (collapse L u) (collapse R v) :=
    ⟨isTree_collapse h.1 hL0 hL1, isTree_collapse h.2.1 hR0 hR1, by have := h.2.2; omega⟩
  refine ⟨hTD, ?_, by omega⟩
  intro x
  obtain ⟨j, hj, hj', y, rfl, hx⟩ := diagramMap_eq_app (collapse R v) hTD.1 hTD.2.2 x
  rw [hx]
  have sL := sorted_collapse h.1 hi hu0 hu1
  have sR := sorted_collapse h.2.1 hi' hv0 hv1
  have lenL := length_collapseList (sorted L) u i hi
  have lenR := length_collapseList (sorted R) v i hi'
  have eL : (sorted (collapse L u))[j] = if h1 : j < i then (sorted L)[j]'(by omega)
      else if j = i then u else (sorted L)[j + 1]'(by rw [sL] at hj; omega) := by
    simp only [sL]; rw [getElem_collapseList _ _ _ hi]
  have eR : (sorted (collapse R v))[j] = if h1 : j < i then (sorted R)[j]'(by omega)
      else if j = i then v else (sorted R)[j + 1]'(by rw [sR] at hj'; omega) := by
    simp only [sR]; rw [getElem_collapseList _ _ _ hi']
  rw [eL, eR]
  split_ifs with h1 h2
  · exact diagramMap_getElem R h.1 j _ _ y
  · cases hy : y 0
    · have : y = app [false] (shift y 1) := by
        rw [← hy]; exact (app_shift (by intro k hk; simp at hk; subst hk; rfl)).symm
      rw [this, ← app_append, ← app_append, ← hu0, ← hv0]
      exact diagramMap_getElem R h.1 i _ _ _
    · have : y = app [true] (shift y 1) := by
        rw [← hy]; exact (app_shift (by intro k hk; simp at hk; subst hk; rfl)).symm
      rw [this, ← app_append, ← app_append, ← hu1, ← hv1]
      exact diagramMap_getElem R h.1 (i + 1) _ _ _
  · exact diagramMap_getElem R h.1 (j + 1) _ _ y

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

lemma refine_cover {L L' : Finset Seq} (hL : IsTree L) (hL' : IsTree L')
    (href : ∀ s' ∈ L', ∃ s ∈ L, s <+: s') {s : Seq} (hs : s ∈ L) : ∃ s'' ∈ L', s <+: s'' := by
  obtain ⟨s'', hs'', h1 | h1⟩ := tree_exists_comparable hL' s
  · obtain ⟨s₀, hs₀, h2⟩ := href s'' hs''
    have e : s₀ = s := tree_eq_of_prefix hL hs₀ hs (h2.trans h1)
    subst e
    exact ⟨s'', hs'', h2⟩
  · exact ⟨s'', hs'', h1⟩

lemma card_le_of_refine {L L' : Finset Seq} (hL : IsTree L) (hL' : IsTree L')
    (href : ∀ s' ∈ L', ∃ s ∈ L, s <+: s') : L.card ≤ L'.card := by
  let f : Seq → Seq := fun s' => if h : ∃ s ∈ L, s <+: s' then h.choose else s'
  apply Finset.card_le_card_of_surjOn f
  intro s hs
  obtain ⟨s'', hs'', hp⟩ := refine_cover hL hL' href hs
  refine ⟨s'', hs'', ?_⟩
  have hex : ∃ s ∈ L, s <+: s'' := ⟨s, hs, hp⟩
  simp only [f, dif_pos hex]
  exact tree_eq_of_comparable hL hex.choose_spec.1 hs
    (List.prefix_or_prefix_of_prefix hex.choose_spec.2 hp)

lemma reduced_iff {S T : Finset Seq} (h : IsTreeDiagram S T) :
    IsReducedDiagram S T ↔ ¬ CommonCaret S T := by
  constructor
  · rintro hred ⟨i, hi, hi', c1, c2, c3, c4⟩
    simp only [List.get_eq_getElem] at c1 c2 c3 c4
    obtain ⟨u, hu0, hu1⟩ := tree_consecutive h.1 hi c1 c3
    obtain ⟨v, hv0, hv1⟩ := tree_consecutive h.2.1 hi' c2 c4
    obtain ⟨hTD, he, hlt⟩ := reduce_step h hi hi' hu0 hu1 hv0 hv1
    have := hred.2 _ _ hTD he
    omega
  · intro hnc
    exact ⟨h, fun L' R' h' he => card_le_of_refine h.1 h'.1 (refine_of_not_commonCaret h hnc h' he)⟩

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
theorem solution (S T : Finset Seq) (h : IsTreeDiagram S T) :
    IsReducedDiagram S T ↔
      ¬ ∃ (i : ℕ) (hi : i + 1 < (sorted S).length) (hi' : i + 1 < (sorted T).length),
        ((sorted S).get ⟨i, by omega⟩).getLast? = some false ∧
        ((sorted T).get ⟨i, by omega⟩).getLast? = some false ∧
        ((sorted S).get ⟨i + 1, hi⟩).getLast? = some true ∧
        ((sorted T).get ⟨i + 1, hi'⟩).getLast? = some true :=
  Dev.Diagrams.reduced_iff h
