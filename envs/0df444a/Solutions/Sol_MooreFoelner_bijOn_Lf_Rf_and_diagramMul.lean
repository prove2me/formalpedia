-- Prove2me | solution 1 for MooreFoelner.bijOn_Lf_Rf_and_diagramMul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T03:39:01.212356+00:00
-- url     : https://prove2.me/submissions/7778b0c7-ce18-402d-86a9-166b7071520e

import Theorems.Thm_MooreFoelner_isReducedDiagram_iff
import Theorems.Thm_MooreFoelner_existsUnique_isReducedDiagram_diagramEquiv
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib
import Theorems.Thm_CannonFloydParry_exists_represents
import Theorems.Thm_CannonFloydParry_exists_isReduced_represents

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

lemma isInitialPart_iff (u : Seq) (x : ℕ → Bool) :
    IsInitialPart u x ↔ ∀ i (h : i < u.length), u[i] = x i := Iff.rfl

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

/-! ### The lexicographic order -/

/-- Neither of `u`, `v` is an initial part of the other. -/
def Incomp (u v : Seq) : Prop := ¬ u <+: v ∧ ¬ v <+: u

lemma Incomp.symm {u v : Seq} (h : Incomp u v) : Incomp v u := ⟨h.2, h.1⟩

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

lemma tree_nonempty {T : Finset Seq} (hT : IsTree T) : T.Nonempty := by
  obtain ⟨t, ht, -⟩ := tree_exists_mem hT (fun _ => false)
  exact ⟨t, ht⟩

lemma isTree_trivialTree : IsTree trivialTree := by
  intro x
  refine ⟨[], ⟨by simp [trivialTree], fun i h => by simp at h⟩, ?_⟩
  rintro t ⟨ht, -⟩
  simpa [trivialTree] using ht

lemma sorted_trivialTree : sorted trivialTree = [[]] :=
  sorted_eq_of (by simp) (by simp [trivialTree])

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

lemma diagramMap_trivial (x : ℕ → Bool) : diagramMap trivialTree trivialTree x = x := by
  have := diagramMap_getElem trivialTree isTree_trivialTree 0 (by simp [sorted_trivialTree])
    (by simp [sorted_trivialTree]) x
  simpa [sorted_trivialTree] using this

lemma diagramMap_swap {L R : Finset Seq} (h : IsTreeDiagram L R) (x : ℕ → Bool) :
    diagramMap R L (diagramMap L R x) = x := by
  obtain ⟨i, hi, hi', y, rfl, hx⟩ := diagramMap_eq_app R h.1 h.2.2 x
  rw [hx, diagramMap_getElem L h.2.1 i hi' hi y]

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

/-! ### Removing a caret -/

/-! ### Diagrams without a common caret -/

/-- The right side of #4: a common caret at some position. -/
def CommonCaret (S T : Finset Seq) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < (sorted S).length) (hi' : i + 1 < (sorted T).length),
    ((sorted S).get ⟨i, by omega⟩).getLast? = some false ∧
    ((sorted T).get ⟨i, by omega⟩).getLast? = some false ∧
    ((sorted S).get ⟨i + 1, hi⟩).getLast? = some true ∧
    ((sorted T).get ⟨i + 1, hi'⟩).getLast? = some true

lemma reduced_iff {S T : Finset Seq} (h : IsTreeDiagram S T) :
    IsReducedDiagram S T ↔ ¬ CommonCaret S T :=
  MooreFoelner.isReducedDiagram_iff S T h

lemma reduced_unique {L R L' R' : Finset Seq} (h1 : IsReducedDiagram L R)
    (h2 : IsReducedDiagram L' R') (he : DiagramEquiv L R L' R') : L = L' ∧ R = R' := by
  have := (MooreFoelner.existsUnique_isReducedDiagram_diagramEquiv L R h1.1).unique
    (y₁ := (L, R)) (y₂ := (L', R')) ⟨h1, fun _ => rfl⟩ ⟨h2, he⟩
  exact Prod.mk.inj this

lemma exists_reduced_equiv {L R : Finset Seq} (h : IsTreeDiagram L R) :
    ∃ L' R', IsReducedDiagram L' R' ∧ DiagramEquiv L R L' R' := by
  obtain ⟨⟨L', R'⟩, ⟨hr, he⟩, -⟩ := MooreFoelner.existsUnique_isReducedDiagram_diagramEquiv L R h
  exact ⟨L', R', hr, he⟩

end MooreFoelner.Dev.Diagrams

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner

namespace MooreFoelner.Dev.Diagrams

open MooreFoelner CannonFloydParry Classical

/-! ### Binary expansions -/

/-- The digits of an infinite binary sequence, in `Fin 2`. -/
def digits2 (x : ℕ → Bool) : ℕ → Fin 2 := fun n => if x n then 1 else 0

/-- The real number `0.x₀x₁x₂…`. -/
noncomputable def val (x : ℕ → Bool) : ℝ := Real.ofDigits (digits2 x)

lemma val_nonneg (x : ℕ → Bool) : 0 ≤ val x := Real.ofDigits_nonneg _

lemma val_le_one (x : ℕ → Bool) : val x ≤ 1 := Real.ofDigits_le_one _

lemma val_cons (b : Bool) (y : ℕ → Bool) :
    val (app [b] y) = (if b then 1 / 2 else 0) + (1 / 2) * val y := by
  unfold val
  rw [Real.ofDigits_eq_sum_add_ofDigits _ 1]
  have : (fun i => digits2 (app [b] y) (i + 1)) = digits2 y := by
    funext i; simp [digits2, app]
  rw [this]
  cases b <;> simp [Real.ofDigitsTerm, digits2, app]

lemma seqVal_nil : seqVal [] = 0 := by simp [seqVal]

lemma seqVal_cons (b : Bool) (u : Seq) :
    seqVal (b :: u) = (if b then 1 / 2 else 0) + (1 / 2) * seqVal u := by
  unfold seqVal
  refine (Fin.sum_univ_succ (n := u.length) (fun i => if (b :: u).get i = true then
    (1 / 2 : ℝ) ^ ((i : ℕ) + 1) else 0)).trans ?_
  simp only [Fin.val_zero, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_zero,
    List.getElem_cons_succ]
  rw [Finset.mul_sum]
  congr 1
  · cases b <;> norm_num
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring

lemma val_app (u : Seq) (y : ℕ → Bool) :
    val (app u y) = seqVal u + (1 / 2) ^ u.length * val y := by
  induction u with
  | nil => simp [seqVal_nil]
  | cons b u ih =>
    rw [show b :: u = [b] ++ u from rfl, app_append, val_cons, ih, List.singleton_append,
      seqVal_cons, List.length_cons, pow_succ]
    ring

lemma val_const_false : val (fun _ => false) = 0 := by
  unfold val Real.ofDigits Real.ofDigitsTerm
  simp [digits2]

lemma val_const_true : val (fun _ => true) = 1 := by
  have h := Real.ofDigits_const_last_eq_one' (b := 2) (by norm_num)
  unfold val
  convert h using 2
  funext n
  apply Fin.ext
  simp [digits2]

lemma val_surj {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) : ∃ y, val y = w := by
  obtain ⟨d, -, hd⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num) hw
  refine ⟨fun n => decide (d n = 1), ?_⟩
  rw [← hd]
  unfold val
  congr 1
  funext n
  simp only [digits2]
  by_cases h : d n = 1
  · simp [h]
  · have : d n = 0 := Fin.ext (by
      have := (d n).isLt
      have h' : (d n).val ≠ 1 := fun e => h (Fin.ext e)
      simp only [Fin.val_zero]; omega)
    simp [this]

lemma seqVal_eq_val (u : Seq) : seqVal u = val (app u (fun _ => false)) := by
  rw [val_app, val_const_false]; ring

lemma seqVal_append (p q : Seq) : seqVal (p ++ q) = seqVal p + (1 / 2) ^ p.length * seqVal q := by
  rw [seqVal_eq_val, seqVal_eq_val q, app_append, val_app]

lemma seqVal_nonneg (u : Seq) : 0 ≤ seqVal u := by
  rw [seqVal_eq_val]; exact val_nonneg _

lemma seqVal_add_le_one (u : Seq) : seqVal u + (1 / 2) ^ u.length ≤ 1 := by
  have := val_le_one (app u (fun _ => true))
  rw [val_app, val_const_true] at this
  simpa using this

lemma seqVal_lt_one (u : Seq) : seqVal u < 1 := by
  have := seqVal_add_le_one u
  have : (0 : ℝ) < (1 / 2) ^ u.length := by positivity
  linarith

lemma seqVal_inj : ∀ {a b : Seq}, a.length = b.length → seqVal a = seqVal b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: a, d :: b, h, he => by
    rw [seqVal_cons, seqVal_cons] at he
    have ha := seqVal_lt_one a
    have hb := seqVal_lt_one b
    have ha0 := seqVal_nonneg a
    have hb0 := seqVal_nonneg b
    cases c <;> cases d <;> simp at he
    · exact congrArg (false :: ·) (seqVal_inj (by simpa using h) (by linarith))
    · linarith
    · linarith
    · exact congrArg (true :: ·) (seqVal_inj (by simpa using h) (by linarith))

lemma val_app_inj {a b : Seq} (h : ∀ z, val (app a z) = val (app b z)) : a = b := by
  have h0 := h (fun _ => false)
  have h1 := h (fun _ => true)
  rw [val_app, val_app, val_const_false] at h0
  rw [val_app, val_app, val_const_true] at h1
  simp only [mul_zero, add_zero, mul_one] at h0 h1
  have hp : (1 / 2 : ℝ) ^ a.length = (1 / 2) ^ b.length := by linarith
  have hl : a.length = b.length :=
    pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hp
  exact seqVal_inj hl h0

/-! ### `Describes` and the map on infinite sequences -/

/-- The point `0.x₀x₁…` of `[0,1]`. -/
noncomputable def toUI (x : ℕ → Bool) : UI := ⟨val x, val_nonneg x, val_le_one x⟩

lemma half_pow_mul_zpow (a b : ℕ) : (1 / 2 : ℝ) ^ a * 2 ^ ((a : ℤ) - b) = (1 / 2) ^ b := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow, one_div_pow]
  field_simp

lemma zpow_eq_mul_half_pow (s t : ℕ) : (2 : ℝ) ^ ((s : ℤ) - t) = 2 ^ s * (1 / 2) ^ t := by
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow]
  field_simp

lemma describes_iff {L R : Finset Seq} (h : IsTreeDiagram L R) (f : UI ≃o UI) :
    Describes L R f ↔ ∀ x, ((f (toUI x) : UI) : ℝ) = val (diagramMap L R x) := by
  constructor
  · intro hd x
    obtain ⟨i, hi, hi', y, rfl, hx⟩ := diagramMap_eq_app R h.1 h.2.2 x
    rw [hx]
    have hy0 := val_nonneg y
    have hy1 := val_le_one y
    have hpos : (0 : ℝ) ≤ (1 / 2) ^ ((sorted L)[i]).length := by positivity
    have := hd.2 i hi hi' (toUI (app (sorted L)[i] y))
      (by simp only [toUI, List.get_eq_getElem, val_app]; nlinarith)
      (by simp only [toUI, List.get_eq_getElem, val_app]; nlinarith)
    rw [this]
    simp only [toUI, List.get_eq_getElem, val_app]
    rw [add_sub_cancel_left, mul_comm ((1 / 2 : ℝ) ^ _) (val y), mul_assoc, half_pow_mul_zpow]
    ring
  · intro hv
    refine ⟨h, fun i hL hR z h1 h2 => ?_⟩
    simp only [List.get_eq_getElem] at h1 h2 ⊢
    set s := (sorted L)[i]
    set t := (sorted R)[i]
    set w := ((z : ℝ) - seqVal s) * 2 ^ s.length with hw
    have hp : (1 / 2 : ℝ) ^ s.length * 2 ^ s.length = 1 := by
      rw [one_div_pow]; field_simp
    have hw0 : 0 ≤ w := by
      have : (0 : ℝ) ≤ 2 ^ s.length := by positivity
      exact mul_nonneg (by linarith) this
    have hw1 : w ≤ 1 := by
      have : (0 : ℝ) ≤ 2 ^ s.length := by positivity
      calc w ≤ (1 / 2) ^ s.length * 2 ^ s.length := mul_le_mul_of_nonneg_right (by linarith) this
        _ = 1 := hp
    obtain ⟨y, hy⟩ := val_surj ⟨hw0, hw1⟩
    have hz : toUI (app s y) = z := by
      apply Subtype.ext
      simp only [toUI, val_app, hy, hw]
      rw [mul_comm ((z : ℝ) - _), ← mul_assoc, hp]; ring
    have key : ((f (toUI (app s y)) : UI) : ℝ) = val (app t y) := by
      rw [hv, diagramMap_getElem R h.1 i hL hR y]
    rw [hz] at key
    rw [key, val_app, hy, hw, zpow_eq_mul_half_pow]
    ring

/-! ### Maps that are locally prefix replacements -/

/-- Near every point, `Φ` replaces an initial part `a` by `b`. -/
def LocPR (Φ : (ℕ → Bool) → (ℕ → Bool)) : Prop :=
  ∀ x, ∃ a b, IsInitialPart a x ∧ ∀ z, Φ (app a z) = app b z

lemma locPR_diagramMap {L R : Finset Seq} (h : IsTreeDiagram L R) : LocPR (diagramMap L R) := by
  intro x
  obtain ⟨i, hi, hi', y, rfl, -⟩ := diagramMap_eq_app R h.1 h.2.2 x
  exact ⟨_, _, isInitialPart_app _ _, diagramMap_getElem R h.1 i hi hi'⟩

lemma locPR_comp {Φ Ψ : (ℕ → Bool) → (ℕ → Bool)} (hΦ : LocPR Φ) (hΨ : LocPR Ψ) :
    LocPR (fun x => Ψ (Φ x)) := by
  intro x
  obtain ⟨a, b, hax, hab⟩ := hΦ x
  obtain ⟨y, rfl⟩ := isInitialPart_iff_exists.mp hax
  obtain ⟨c, d, hcx, hcd⟩ := hΨ (app b y)
  rcases comparable_of_isInitialPart hcx (isInitialPart_app b y) with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · refine ⟨a, d ++ w, hax, fun z => ?_⟩
    simp only
    rw [hab, app_append, hcd, app_append]
  · have hw : IsInitialPart w y := isInitialPart_append_app.mp hcx
    refine ⟨a ++ w, d, isInitialPart_append_app.mpr hw, fun z => ?_⟩
    simp only
    rw [app_append, hab, ← app_append, hcd]

lemma eq_of_locPR_aux {Φ Ψ : (ℕ → Bool) → (ℕ → Bool)} (h : ∀ x, val (Φ x) = val (Ψ x))
    {a b c d : Seq} (hab : ∀ z, Φ (app a z) = app b z) (hcd : ∀ z, Ψ (app c z) = app d z)
    (hac : a <+: c) {x : ℕ → Bool} (hcx : IsInitialPart c x) : Φ x = Ψ x := by
  obtain ⟨w, rfl⟩ := hac
  have key : b ++ w = d := by
    apply val_app_inj
    intro z
    rw [← hcd, ← h, app_append a w, hab, app_append]
  obtain ⟨y, rfl⟩ := isInitialPart_iff_exists.mp hcx
  rw [hcd, app_append, hab, ← app_append, key]

lemma eq_of_locPR {Φ Ψ : (ℕ → Bool) → (ℕ → Bool)} (hΦ : LocPR Φ) (hΨ : LocPR Ψ)
    (h : ∀ x, val (Φ x) = val (Ψ x)) : Φ = Ψ := by
  funext x
  obtain ⟨a, b, hax, hab⟩ := hΦ x
  obtain ⟨c, d, hcx, hcd⟩ := hΨ x
  rcases comparable_of_isInitialPart hax hcx with hac | hca
  · exact eq_of_locPR_aux h hab hcd hac hcx
  · exact (eq_of_locPR_aux (fun x => (h x).symm) hcd hab hca hax).symm

/-! ### Consequences for diagrams describing maps -/

lemma describes_of_equiv {L R L' R' : Finset Seq} {f : UI ≃o UI} (hd : Describes L R f)
    (h' : IsTreeDiagram L' R') (he : DiagramEquiv L R L' R') : Describes L' R' f := by
  rw [describes_iff h'] ; intro x
  rw [← he x]; exact (describes_iff hd.1 f).mp hd x

lemma toUI_eq {L R : Finset Seq} {f : UI ≃o UI} (hd : Describes L R f) (x : ℕ → Bool) :
    f (toUI x) = toUI (diagramMap L R x) :=
  Subtype.ext ((describes_iff hd.1 f).mp hd x)

lemma diagramEquiv_of_describes {L R L' R' : Finset Seq} {f : UI ≃o UI} (hd : Describes L R f)
    (hd' : Describes L' R' f) : DiagramEquiv L R L' R' := by
  have := eq_of_locPR (locPR_diagramMap hd.1) (locPR_diagramMap hd'.1) (fun x => by
    rw [← (describes_iff hd.1 f).mp hd x, ← (describes_iff hd'.1 f).mp hd' x])
  exact fun x => congrFun this x

lemma eq_of_describes {L R : Finset Seq} {f g : UI ≃o UI} (hf : Describes L R f)
    (hg : Describes L R g) : f = g := by
  ext z
  obtain ⟨y, hy⟩ := val_surj z.2
  have hz : toUI y = z := Subtype.ext hy
  rw [← hz, toUI_eq hf, toUI_eq hg]

lemma describes_comp {L R L' R' L'' R'' : Finset Seq} {f g : UI ≃o UI} (hf : Describes L R f)
    (hg : Describes L' R' g) (h'' : IsTreeDiagram L'' R'')
    (hc : ∀ x, diagramMap L'' R'' x = diagramMap L' R' (diagramMap L R x)) :
    Describes L'' R'' (f.trans g) := by
  rw [describes_iff h'']
  intro x
  rw [OrderIso.trans_apply, toUI_eq hf, toUI_eq hg, hc]
  rfl

/-! ### Cannon–Floyd–Parry's trees as sets of leaf addresses -/

/-- The addresses of the leaves of a CFP tree, left to right. -/
def addrs : TTree → List Seq
  | .leaf => [[]]
  | .node l r => (addrs l).map (List.cons false) ++ (addrs r).map (List.cons true)

lemma length_addrs : ∀ t : TTree, (addrs t).length = t.leafCount
  | .leaf => rfl
  | .node l r => by simp [addrs, TTree.leafCount, length_addrs l, length_addrs r]

lemma addrs_pairwise : ∀ t : TTree, (addrs t).Pairwise (· < ·)
  | .leaf => by simp [addrs]
  | .node l r => by
    rw [addrs, List.pairwise_append, List.pairwise_map, List.pairwise_map]
    refine ⟨(addrs_pairwise l).imp (fun h => (append_lt_append_left_iff [false]).mpr h),
      (addrs_pairwise r).imp (fun h => (append_lt_append_left_iff [true]).mpr h), ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact append_false_lt_append_true [] a b

lemma isInitialPart_cons {c : Bool} {a : Seq} {x : ℕ → Bool} :
    IsInitialPart (c :: a) x ↔ x 0 = c ∧ IsInitialPart a (shift x 1) := by
  simp only [isInitialPart_iff]
  constructor
  · intro h
    refine ⟨(h 0 (by simp)).symm, fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simpa [shift] using this
  · rintro ⟨h0, h1⟩ i hi
    cases i with
    | zero => simpa using h0.symm
    | succ i =>
      have := h1 i (by simpa using hi)
      simpa [shift] using this

/-- The tree with left subtree `T0` and right subtree `T1`. -/
def join (T0 T1 : Finset Seq) : Finset Seq :=
  T0.image (List.cons false) ∪ T1.image (List.cons true)

lemma isTree_join {T0 T1 : Finset Seq} (h0 : IsTree T0) (h1 : IsTree T1) :
    IsTree (join T0 T1) := by
  intro x
  have hT : IsTree (if x 0 then T1 else T0) := by split <;> assumption
  obtain ⟨a, ⟨ha, hax⟩, hu⟩ := hT (shift x 1)
  refine ⟨x 0 :: a, ⟨?_, isInitialPart_cons.mpr ⟨rfl, hax⟩⟩, ?_⟩
  · simp only [join, Finset.mem_union, Finset.mem_image]
    cases hx : x 0 <;> rw [hx] at ha <;> simp only [Bool.false_eq_true, if_false, if_true] at ha
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩
  · rintro t ⟨ht, htx⟩
    simp only [join, Finset.mem_union, Finset.mem_image] at ht
    rcases ht with ⟨a', ha', rfl⟩ | ⟨a', ha', rfl⟩
    · obtain ⟨hc, ha'x⟩ := isInitialPart_cons.mp htx
      rw [hu a' ⟨by rw [hc]; simpa using ha', ha'x⟩, hc]
    · obtain ⟨hc, ha'x⟩ := isInitialPart_cons.mp htx
      rw [hu a' ⟨by rw [hc]; simpa using ha', ha'x⟩, hc]

/-- `T/b`: the subtree below the digit `b`. -/
def part (T : Finset Seq) (b : Bool) : Finset Seq :=
  (T.filter (fun u => u.head? = some b)).image List.tail

lemma mem_part {T : Finset Seq} {b : Bool} {a : Seq} : a ∈ part T b ↔ b :: a ∈ T := by
  simp only [part, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hh⟩, rfl⟩
    cases u with
    | nil => simp at hh
    | cons c u => simp at hh; subst hh; simpa using hu
  · intro h
    exact ⟨b :: a, ⟨h, rfl⟩, rfl⟩

lemma isTree_part {T : Finset Seq} (hT : IsTree T) (hnil : [] ∉ T) (b : Bool) :
    IsTree (part T b) := by
  intro x
  obtain ⟨t, ⟨ht, htx⟩, hu⟩ := hT (app [b] x)
  have hsx : shift (app [b] x) 1 = x := shift_app [b] x
  cases t with
  | nil => exact absurd ht hnil
  | cons c a =>
    obtain ⟨hc, hax⟩ := isInitialPart_cons.mp htx
    have hc' : c = b := by rw [← hc]; simp [app]
    subst hc'
    refine ⟨a, ⟨mem_part.mpr ht, hsx ▸ hax⟩, ?_⟩
    rintro a' ⟨ha', ha'x⟩
    have := hu (c :: a') ⟨mem_part.mp ha', isInitialPart_cons.mpr ⟨by simp [app], by
      rw [hsx]; exact ha'x⟩⟩
    simpa using this

lemma eq_join_part {T : Finset Seq} (hnil : [] ∉ T) : T = join (part T false) (part T true) := by
  ext u
  cases u with
  | nil => simp [join, hnil]
  | cons c a => cases c <;> simp [join, mem_part]

lemma toFinset_addrs_node (l r : TTree) :
    (addrs (.node l r)).toFinset = join (addrs l).toFinset (addrs r).toFinset := by
  ext u; simp [addrs, join]

lemma isTree_addrs : ∀ t : TTree, IsTree (addrs t).toFinset
  | .leaf => by
    have : (addrs .leaf).toFinset = trivialTree := by simp [addrs, trivialTree]
    rw [this]; exact isTree_trivialTree
  | .node l r => by
    rw [toFinset_addrs_node]; exact isTree_join (isTree_addrs l) (isTree_addrs r)

lemma sorted_addrs (t : TTree) : sorted (addrs t).toFinset = addrs t :=
  sorted_eq_of (addrs_pairwise t) (by simp)

lemma card_addrs (t : TTree) : (addrs t).toFinset.card = t.leafCount := by
  rw [List.toFinset_card_of_nodup ((addrs_pairwise t).imp ne_of_lt), length_addrs]

lemma exists_addrs (n : ℕ) : ∀ {T : Finset Seq}, IsTree T → (∀ u ∈ T, u.length ≤ n) →
    ∃ t, (addrs t).toFinset = T := by
  induction n with
  | zero =>
    intro T hT hn
    obtain ⟨u, hu⟩ := tree_nonempty hT
    have : u = [] := List.eq_nil_of_length_eq_zero (by have := hn u hu; omega)
    subst this
    refine ⟨.leaf, ?_⟩
    ext v; simp only [addrs, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton]
    constructor
    · rintro rfl; exact hu
    · intro hv; exact (tree_eq_of_prefix hT hu hv List.nil_prefix).symm
  | succ n ih =>
    intro T hT hn
    by_cases hnil : [] ∈ T
    · refine ⟨.leaf, ?_⟩
      ext v; simp only [addrs, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.mem_singleton]
      constructor
      · rintro rfl; exact hnil
      · intro hv; exact (tree_eq_of_prefix hT hnil hv List.nil_prefix).symm
    · have hb : ∀ b, ∀ u ∈ part T b, u.length ≤ n := by
        intro b u hu
        have := hn _ (mem_part.mp hu)
        simp at this; omega
      obtain ⟨l, hl⟩ := ih (isTree_part hT hnil false) (hb false)
      obtain ⟨r, hr⟩ := ih (isTree_part hT hnil true) (hb true)
      refine ⟨.node l r, ?_⟩
      rw [toFinset_addrs_node, hl, hr, ← eq_join_part hnil]

lemma exists_addrs_of_isTree {T : Finset Seq} (hT : IsTree T) : ∃ t, (addrs t).toFinset = T :=
  exists_addrs (T.sup List.length) hT (fun _ hu => Finset.le_sup (f := List.length) hu)

/-! ### `marks` and `seqVal` -/

lemma marksAux_addrs : ∀ (t : TTree) (p : Seq),
    seqVal p :: t.marksAux (seqVal p) (seqVal p + (1 / 2) ^ p.length) =
        (addrs t).map (fun s => seqVal (p ++ s)) ∧
      t.marksAux (seqVal p) (seqVal p + (1 / 2) ^ p.length) ++ [seqVal p + (1 / 2) ^ p.length] =
        (addrs t).map (fun s => seqVal (p ++ s) + (1 / 2) ^ (p ++ s).length)
  | .leaf, p => by simp [TTree.marksAux, addrs]
  | .node l r, p => by
    have e1 : seqVal (p ++ [false]) = seqVal p := by
      rw [seqVal_append]; simp [seqVal_cons, seqVal_nil]
    have e2 : seqVal (p ++ [true]) = seqVal p + (1 / 2) ^ (p.length + 1) := by
      rw [seqVal_append]; simp [seqVal_cons, seqVal_nil, pow_succ]
    have hm : (seqVal p + (seqVal p + (1 / 2) ^ p.length)) / 2 = seqVal (p ++ [true]) := by
      rw [e2, pow_succ]; ring
    have hl0 : seqVal (p ++ [false]) + (1 / 2) ^ (p ++ [false]).length = seqVal (p ++ [true]) := by
      rw [e1, e2]; simp
    have hr0 : seqVal (p ++ [true]) + (1 / 2) ^ (p ++ [true]).length =
        seqVal p + (1 / 2) ^ p.length := by
      rw [e2]; simp [pow_succ]; ring
    obtain ⟨Al1, Al2⟩ := marksAux_addrs l (p ++ [false])
    obtain ⟨Ar1, Ar2⟩ := marksAux_addrs r (p ++ [true])
    rw [hl0, e1] at Al1 Al2
    rw [hr0] at Ar1 Ar2
    simp only [TTree.marksAux]
    rw [hm]
    have ha : ∀ s : Seq, (p ++ [false]) ++ s = p ++ false :: s := by simp
    have hb : ∀ s : Seq, (p ++ [true]) ++ s = p ++ true :: s := by simp
    simp only [ha, hb] at Al1 Al2 Ar1 Ar2
    constructor
    · rw [← List.cons_append, Al1, Ar1]
      simp [addrs, List.map_append, List.map_map, Function.comp_def]
    · have : ∀ (A B : List ℝ) (m b : ℝ), (A ++ m :: B) ++ [b] = (A ++ [m]) ++ (B ++ [b]) := by
        intros; simp
      rw [this, Al2, Ar2]
      simp [addrs, List.map_append, List.map_map, Function.comp_def]

lemma marks_eq (t : TTree) :
    t.marks = (addrs t).map seqVal ++ [1] ∧
      t.marks.tail = (addrs t).map (fun s => seqVal s + (1 / 2) ^ s.length) := by
  obtain ⟨h1, h2⟩ := marksAux_addrs t []
  simp only [seqVal_nil, List.length_nil, pow_zero, zero_add, List.nil_append] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [TTree.marks, ← List.cons_append, h1]
  · rw [TTree.marks, List.tail_cons, h2]

lemma marks_getElem (t : TTree) (i : ℕ) (hi : i < (addrs t).length) :
    ∃ (h0 : i < t.marks.length) (h1 : i + 1 < t.marks.length),
      t.marks[i] = seqVal (addrs t)[i] ∧
        t.marks[i + 1] = seqVal (addrs t)[i] + (1 / 2) ^ ((addrs t)[i]).length := by
  obtain ⟨e1, e2⟩ := marks_eq t
  have hlen : t.marks.length = (addrs t).length + 1 := by rw [e1]; simp
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [List.getElem_of_eq e1, List.getElem_append_left (by simpa using hi)]
    simp
  · have : t.marks[i + 1] = t.marks.tail[i]'(by simp; omega) := by
      rw [List.getElem_tail]
    rw [this, List.getElem_of_eq e2]
    simp

lemma describes_of_represents_aux {d : TreeDiagram} {f : UI ≃o UI} (h : Represents d f) (i : ℕ)
    (hL : i < (addrs d.dom).length) (hR : i < (addrs d.ran).length) (z : UI)
    (h1 : seqVal (addrs d.dom)[i] ≤ (z : ℝ))
    (h2 : (z : ℝ) ≤ seqVal (addrs d.dom)[i] + (1 / 2) ^ ((addrs d.dom)[i]).length) :
    ((f z : UI) : ℝ) = seqVal (addrs d.ran)[i] + ((z : ℝ) - seqVal (addrs d.dom)[i]) *
      (2 : ℝ) ^ ((((addrs d.dom)[i]).length : ℤ) - ((addrs d.ran)[i]).length) := by
  obtain ⟨-, haff, hmap⟩ := h
  obtain ⟨hM0, hM1, eM0, eM1⟩ := marks_getElem d.dom i hL
  obtain ⟨hN0, hN1, eN0, eN1⟩ := marks_getElem d.ran i hR
  set s := (addrs d.dom)[i]
  set t := (addrs d.ran)[i]
  obtain ⟨a, c, hac⟩ := List.isChain_iff_getElem.mp haff i hM1
  have hmap0 : extend f d.dom.marks[i] = d.ran.marks[i] := by
    have := List.getElem_of_eq hmap (i := i) (by simpa using hM0)
    simpa using this
  have hmap1 : extend f d.dom.marks[i + 1] = d.ran.marks[i + 1] := by
    have := List.getElem_of_eq hmap (i := i + 1) (by simpa using hM1)
    simpa using this
  have hpos : (0 : ℝ) < (1 / 2) ^ s.length := by positivity
  have hle : d.dom.marks[i] ≤ d.dom.marks[i + 1] := by rw [eM0, eM1]; linarith
  have A0 := hac _ ⟨le_rfl, hle⟩
  have A1 := hac _ ⟨hle, le_rfl⟩
  have Az := hac z ⟨by rw [eM0]; exact h1, by rw [eM1]; exact h2⟩
  rw [hmap0] at A0
  rw [hmap1] at A1
  rw [eM0, eN0] at A0
  rw [eM1, eN1] at A1
  have hfz : extend f (z : ℝ) = ((f z : UI) : ℝ) := by
    rw [extend_apply, extendFun_of_mem f z.2]
  rw [← hfz, Az]
  have ha : a * (1 / 2) ^ s.length = (1 / 2) ^ t.length := by linarith
  have ha' : a = 2 ^ s.length * (1 / 2) ^ t.length := by
    have h2s : (1 / 2 : ℝ) ^ s.length * 2 ^ s.length = 1 := by rw [one_div_pow]; field_simp
    calc a = a * ((1 / 2) ^ s.length * 2 ^ s.length) := by rw [h2s, mul_one]
      _ = 2 ^ s.length * (1 / 2) ^ t.length := by rw [← mul_assoc, ha]; ring
  rw [zpow_eq_mul_half_pow, ← ha']
  linarith

lemma describes_of_represents {d : TreeDiagram} {f : UI ≃o UI} (h : Represents d f) :
    Describes (addrs d.dom).toFinset (addrs d.ran).toFinset f := by
  refine ⟨⟨isTree_addrs _, isTree_addrs _, by rw [card_addrs, card_addrs, d.leaves_eq]⟩, ?_⟩
  intro i hL hR z h1 h2
  have hL' : i < (addrs d.dom).length := by rwa [sorted_addrs] at hL
  have hR' : i < (addrs d.ran).length := by rwa [sorted_addrs] at hR
  have eL : (sorted (addrs d.dom).toFinset).get ⟨i, hL⟩ = (addrs d.dom)[i] := by
    simp only [List.get_eq_getElem]; exact List.getElem_of_eq (sorted_addrs _) _
  have eR : (sorted (addrs d.ran).toFinset).get ⟨i, hR⟩ = (addrs d.ran)[i] := by
    simp only [List.get_eq_getElem]; exact List.getElem_of_eq (sorted_addrs _) _
  rw [eL] at h1 h2 ⊢
  rw [eR]
  exact describes_of_represents_aux h i hL' hR' z h1 h2

lemma exists_describes {L R : Finset Seq} (h : IsTreeDiagram L R) : ∃ f ∈ F, Describes L R f := by
  obtain ⟨tL, htL⟩ := exists_addrs_of_isTree h.1
  obtain ⟨tR, htR⟩ := exists_addrs_of_isTree h.2.1
  have hc : tL.leafCount = tR.leafCount := by
    rw [← card_addrs, ← card_addrs, htL, htR]; exact h.2.2
  obtain ⟨f, hf⟩ := CannonFloydParry.exists_represents ⟨tL, tR, hc⟩
  refine ⟨f, hf.1, ?_⟩
  have := describes_of_represents hf
  rw [← htL, ← htR]
  exact this

lemma exists_describes_of_mem {f : UI ≃o UI} (hf : f ∈ F) : ∃ L R, Describes L R f := by
  obtain ⟨d, -, hd⟩ := CannonFloydParry.exists_isReduced_represents hf
  exact ⟨_, _, describes_of_represents hd⟩

/-! ### Reduced diagrams and Thompson's group -/

lemma toMap_mem (f : MooreF) : toMap f ∈ F := (MulOpposite.unop f).2

lemma toMap_mul (f g : MooreF) : toMap (f * g) = (toMap f).trans (toMap g) := by
  simp only [toMap, MulOpposite.unop_mul, Subgroup.coe_mul]
  rfl

lemma toMap_injective : Function.Injective toMap := by
  intro f g h
  exact MulOpposite.unop_injective (Subtype.ext h)

lemma exists_reduced_describes {g : UI ≃o UI} (hg : g ∈ F) :
    ∃ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 ∧ Describes D.1 D.2 g := by
  obtain ⟨L, R, hd⟩ := exists_describes_of_mem hg
  obtain ⟨L', R', hr, he⟩ := exists_reduced_equiv hd.1
  exact ⟨(L', R'), hr, describes_of_equiv hd hr.1 he⟩

lemma reducedDiagram_spec {g : UI ≃o UI} (hg : g ∈ F) :
    IsReducedDiagram (reducedDiagram g).1 (reducedDiagram g).2 ∧
      Describes (reducedDiagram g).1 (reducedDiagram g).2 g :=
  Classical.epsilon_spec (exists_reduced_describes hg)

lemma eq_of_reduced_describes {D D' : Finset Seq × Finset Seq} {g : UI ≃o UI}
    (hr : IsReducedDiagram D.1 D.2) (hd : Describes D.1 D.2 g) (hr' : IsReducedDiagram D'.1 D'.2)
    (hd' : Describes D'.1 D'.2 g) : D = D' := by
  obtain ⟨e1, e2⟩ := reduced_unique hr hr' (diagramEquiv_of_describes hd hd')
  exact Prod.ext e1 e2

lemma eq_of_reduced_equiv {D D' : Finset Seq × Finset Seq} (hr : IsReducedDiagram D.1 D.2)
    (hr' : IsReducedDiagram D'.1 D'.2) (he : ∀ x, diagramMap D.1 D.2 x = diagramMap D'.1 D'.2 x) :
    D = D' := by
  obtain ⟨e1, e2⟩ := reduced_unique hr hr' he
  exact Prod.ext e1 e2

lemma exists_comp {D D' : Finset Seq × Finset Seq} (hD : IsReducedDiagram D.1 D.2)
    (hD' : IsReducedDiagram D'.1 D'.2) : ∃ E : Finset Seq × Finset Seq, IsReducedDiagram E.1 E.2 ∧
      ∀ x, diagramMap E.1 E.2 x = diagramMap D'.1 D'.2 (diagramMap D.1 D.2 x) := by
  obtain ⟨f, hf, hdf⟩ := exists_describes hD.1
  obtain ⟨g, hg, hdg⟩ := exists_describes hD'.1
  have hgf : f.trans g ∈ F := by
    have : f.trans g = g * f := rfl
    rw [this]; exact F.mul_mem hg hf
  obtain ⟨E, hE, hdE⟩ := exists_reduced_describes hgf
  refine ⟨E, hE, fun x => ?_⟩
  have := eq_of_locPR (locPR_diagramMap hE.1)
    (locPR_comp (locPR_diagramMap hD.1) (locPR_diagramMap hD'.1)) (fun x => by
      rw [← (describes_iff hE.1 _).mp hdE x, OrderIso.trans_apply, toUI_eq hdf, toUI_eq hdg]
      rfl)
  exact congrFun this x

lemma diagramMul_spec {D D' : Finset Seq × Finset Seq} (hD : IsReducedDiagram D.1 D.2)
    (hD' : IsReducedDiagram D'.1 D'.2) :
    IsReducedDiagram (diagramMul D D').1 (diagramMul D D').2 ∧
      ∀ x, diagramMap (diagramMul D D').1 (diagramMul D D').2 x =
        diagramMap D'.1 D'.2 (diagramMap D.1 D.2 x) :=
  Classical.epsilon_spec (exists_comp hD hD')

lemma isReducedDiagram_trivial : IsReducedDiagram trivialTree trivialTree := by
  refine ⟨⟨isTree_trivialTree, isTree_trivialTree, rfl⟩, fun L' R' h' _ => ?_⟩
  have : trivialTree.card = 1 := rfl
  rw [this]
  exact Finset.card_pos.mpr (tree_nonempty h'.1)

lemma commonCaret_swap {S T : Finset Seq} (h : CommonCaret S T) : CommonCaret T S := by
  obtain ⟨i, hi, hi', c1, c2, c3, c4⟩ := h
  exact ⟨i, hi', hi, c2, c1, c4, c3⟩

lemma isReducedDiagram_swap {S T : Finset Seq} (h : IsReducedDiagram S T) :
    IsReducedDiagram T S := by
  have hs : IsTreeDiagram T S := ⟨h.1.2.1, h.1.1, h.1.2.2.symm⟩
  rw [reduced_iff hs]
  intro hc
  exact (reduced_iff h.1).mp h (commonCaret_swap hc)

end MooreFoelner.Dev.Diagrams

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open MooreFoelner CannonFloydParry Classical in
open Classical CannonFloydParry in
open MooreFoelner CannonFloydParry Classical in
open Classical CannonFloydParry in
open Dev.Diagrams in
theorem solution :
    (∀ D D' : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 → IsReducedDiagram D'.1 D'.2 →
        IsReducedDiagram (diagramMul D D').1 (diagramMul D D').2 ∧
          ∀ x, diagramMap (diagramMul D D').1 (diagramMul D D').2 x =
            diagramMap D'.1 D'.2 (diagramMap D.1 D.2 x)) ∧
    (∀ D D' D'' : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 → IsReducedDiagram D'.1 D'.2 →
        IsReducedDiagram D''.1 D''.2 →
        diagramMul (diagramMul D D') D'' = diagramMul D (diagramMul D' D'')) ∧
    IsReducedDiagram trivialTree trivialTree ∧
    (∀ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 →
        diagramMul (trivialTree, trivialTree) D = D ∧ diagramMul D (trivialTree, trivialTree) = D) ∧
    (∀ D : Finset Seq × Finset Seq, IsReducedDiagram D.1 D.2 →
        IsReducedDiagram D.2 D.1 ∧ diagramMul D (D.2, D.1) = (trivialTree, trivialTree) ∧
          diagramMul (D.2, D.1) D = (trivialTree, trivialTree)) ∧
    Set.BijOn (fun f : MooreF => (Lf (toMap f), Rf (toMap f))) Set.univ
        {D : Finset Seq × Finset Seq | IsReducedDiagram D.1 D.2} ∧
      (∀ f : MooreF, Describes (Lf (toMap f)) (Rf (toMap f)) (toMap f)) ∧
      ∀ f g : MooreF, (Lf (toMap (f * g)), Rf (toMap (f * g))) =
        diagramMul (Lf (toMap f), Rf (toMap f)) (Lf (toMap g), Rf (toMap g)) := by
  have hT : IsReducedDiagram (trivialTree, trivialTree).1 (trivialTree, trivialTree).2 :=
    isReducedDiagram_trivial
  refine ⟨fun D D' hD hD' => diagramMul_spec hD hD', ?_, isReducedDiagram_trivial, ?_, ?_, ?_, ?_, ?_⟩
  · -- associativity
    intro D D' D'' hD hD' hD''
    obtain ⟨h1, m1⟩ := diagramMul_spec hD hD'
    obtain ⟨h2, m2⟩ := diagramMul_spec hD' hD''
    obtain ⟨h3, m3⟩ := diagramMul_spec h1 hD''
    obtain ⟨h4, m4⟩ := diagramMul_spec hD h2
    apply eq_of_reduced_equiv h3 h4
    intro x
    rw [m3, m4, m1, m2]
  · -- identity
    intro D hD
    obtain ⟨h1, m1⟩ := diagramMul_spec hT hD
    obtain ⟨h2, m2⟩ := diagramMul_spec hD hT
    refine ⟨eq_of_reduced_equiv h1 hD (fun x => ?_), eq_of_reduced_equiv h2 hD (fun x => ?_)⟩
    · rw [m1, diagramMap_trivial]
    · rw [m2, diagramMap_trivial]
  · -- inverses
    intro D hD
    have hS : IsReducedDiagram (D.2, D.1).1 (D.2, D.1).2 := isReducedDiagram_swap hD
    obtain ⟨h1, m1⟩ := diagramMul_spec hD hS
    obtain ⟨h2, m2⟩ := diagramMul_spec hS hD
    refine ⟨hS, eq_of_reduced_equiv h1 hT (fun x => ?_), eq_of_reduced_equiv h2 hT (fun x => ?_)⟩
    · rw [m1, diagramMap_trivial]
      exact diagramMap_swap hD.1 x
    · rw [m2, diagramMap_trivial]
      exact diagramMap_swap hS.1 x
  · -- the bijection
    refine ⟨fun f _ => (reducedDiagram_spec (toMap_mem f)).1, ?_, ?_⟩
    · intro f _ g _ hfg
      apply toMap_injective
      have hf := (reducedDiagram_spec (toMap_mem f)).2
      have hg := (reducedDiagram_spec (toMap_mem g)).2
      have e : reducedDiagram (toMap f) = reducedDiagram (toMap g) := hfg
      rw [e] at hf
      exact eq_of_describes hf hg
    · intro D hD
      obtain ⟨g, hg, hdg⟩ := exists_describes hD.1
      refine ⟨MulOpposite.op ⟨g, hg⟩, Set.mem_univ _, ?_⟩
      have hspec := reducedDiagram_spec (g := toMap (MulOpposite.op ⟨g, hg⟩)) (toMap_mem _)
      exact eq_of_reduced_describes hspec.1 hspec.2 hD hdg
  · intro f
    exact (reducedDiagram_spec (toMap_mem f)).2
  · intro f g
    have hf := reducedDiagram_spec (toMap_mem f)
    have hg := reducedDiagram_spec (toMap_mem g)
    have hfg := reducedDiagram_spec (toMap_mem (f * g))
    obtain ⟨h1, m1⟩ := diagramMul_spec hf.1 hg.1
    have hd := describes_comp hf.2 hg.2 h1.1 m1
    rw [← toMap_mul] at hd
    exact eq_of_reduced_describes hfg.1 hfg.2 h1 hd
