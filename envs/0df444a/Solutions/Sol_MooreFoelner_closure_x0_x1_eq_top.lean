-- Prove2me | solution 1 for MooreFoelner.closure_x0_x1_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T03:55:24.683426+00:00
-- url     : https://prove2.me/submissions/b6cf9f4e-54bd-4055-b38a-7a5544b81bc4

import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F

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

lemma app_shift {u : Seq} {x : ℕ → Bool} (h : IsInitialPart u x) : app u (shift x u.length) = x := by
  funext n
  simp only [app, shift]
  split_ifs with hn
  · exact h n hn
  · congr 1; omega

lemma isInitialPart_iff_exists {u : Seq} {x : ℕ → Bool} :
    IsInitialPart u x ↔ ∃ y, x = app u y :=
  ⟨fun h => ⟨_, (app_shift h).symm⟩, fun ⟨y, hy⟩ => hy ▸ isInitialPart_app u y⟩

/-! ### The lexicographic order -/

/-- Neither of `u`, `v` is an initial part of the other. -/
def Incomp (u v : Seq) : Prop := ¬ u <+: v ∧ ¬ v <+: u

lemma Incomp.symm {u v : Seq} (h : Incomp u v) : Incomp v u := ⟨h.2, h.1⟩

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

/-! ### Removing a caret -/

/-! ### Diagrams without a common caret -/

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

/-! ### Consequences for diagrams describing maps -/

lemma toUI_eq {L R : Finset Seq} {f : UI ≃o UI} (hd : Describes L R f) (x : ℕ → Bool) :
    f (toUI x) = toUI (diagramMap L R x) :=
  Subtype.ext ((describes_iff hd.1 f).mp hd x)

lemma eq_of_describes {L R : Finset Seq} {f g : UI ≃o UI} (hf : Describes L R f)
    (hg : Describes L R g) : f = g := by
  ext z
  obtain ⟨y, hy⟩ := val_surj z.2
  have hz : toUI y = z := Subtype.ext hy
  rw [← hz, toUI_eq hf, toUI_eq hg]

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

section
/-!
# Moore 2013, group Gen: `F` is generated by `{x₀, x₁}` (p. 4)

`toMap x₀ = A⁻¹` and `toMap x₁ = B⁻¹` for Cannon–Floyd–Parry's `A`, `B`; their closure theorem
then transports through `MulOpposite.op`.
-/

namespace MooreFoelner.Dev.Gen

open Classical MooreFoelner CannonFloydParry MooreFoelner.Dev.Diagrams

lemma isInitialPart_nil (x : ℕ → Bool) : IsInitialPart [] x :=
  fun _ h => absurd h (Nat.not_lt_zero _)

lemma isInitialPart_cons_iff (b : Bool) (s : Seq) (x : ℕ → Bool) :
    IsInitialPart (b :: s) x ↔ x 0 = b ∧ IsInitialPart s (shift x 1) := by
  constructor
  · intro h
    refine ⟨(h 0 (by simp)).symm, fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simpa [shift] using this
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · simp [h0]
    · have := h i (by simp at hi; omega)
      simpa [shift] using this

/-- A tree given by an explicit list of leaves, checked digit by digit. -/
lemma isTree_of_check (T : Finset Seq)
    (h : ∀ x : ℕ → Bool, ∃ t ∈ T, IsInitialPart t x ∧ ∀ t' ∈ T, IsInitialPart t' x → t' = t) :
    IsTree T := fun x => by
  obtain ⟨t, ht, hx, hu⟩ := h x
  exact ⟨t, ⟨ht, hx⟩, fun t' ⟨h1, h2⟩ => hu t' h1 h2⟩

lemma bits_00 : bits "00" = [false, false] := rfl
lemma bits_01 : bits "01" = [false, true] := rfl
lemma bits_1 : bits "1" = [true] := rfl
lemma bits_0 : bits "0" = [false] := rfl
lemma bits_10 : bits "10" = [true, false] := rfl
lemma bits_11 : bits "11" = [true, true] := rfl
lemma bits_100 : bits "100" = [true, false, false] := rfl
lemma bits_101 : bits "101" = [true, false, true] := rfl
lemma bits_110 : bits "110" = [true, true, false] := rfl
lemma bits_111 : bits "111" = [true, true, true] := rfl

noncomputable def x0L : Finset Seq := {bits "00", bits "01", bits "1"}
noncomputable def x0R : Finset Seq := {bits "0", bits "10", bits "11"}
noncomputable def x1L : Finset Seq := {bits "0", bits "100", bits "101", bits "11"}
noncomputable def x1R : Finset Seq := {bits "0", bits "10", bits "110", bits "111"}

lemma isTree_x0L : IsTree x0L := by
  apply isTree_of_check
  intro x
  simp only [x0L, bits_00, bits_01, bits_1, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> simp

lemma isTree_x0R : IsTree x0R := by
  apply isTree_of_check
  intro x
  simp only [x0R, bits_0, bits_10, bits_11, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> simp

lemma isTree_x1L : IsTree x1L := by
  apply isTree_of_check
  intro x
  simp only [x1L, bits_0, bits_100, bits_101, bits_11, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> rcases x 2 <;> simp

lemma isTree_x1R : IsTree x1R := by
  apply isTree_of_check
  intro x
  simp only [x1R, bits_0, bits_10, bits_110, bits_111, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
    isInitialPart_cons_iff, isInitialPart_nil, shift]
  rcases x 0 <;> rcases x 1 <;> rcases x 2 <;> simp

lemma sorted_x0L : sorted x0L = [[false, false], [false, true], [true]] := by
  apply sorted_eq_of
  · decide
  · intro a; simp [x0L, bits_00, bits_01, bits_1]

lemma sorted_x0R : sorted x0R = [[false], [true, false], [true, true]] := by
  apply sorted_eq_of
  · decide
  · intro a; simp [x0R, bits_0, bits_10, bits_11]

lemma sorted_x1L :
    sorted x1L = [[false], [true, false, false], [true, false, true], [true, true]] := by
  apply sorted_eq_of
  · decide
  · intro a; simp [x1L, bits_0, bits_100, bits_101, bits_11]

lemma sorted_x1R :
    sorted x1R = [[false], [true, false], [true, true, false], [true, true, true]] := by
  apply sorted_eq_of
  · decide
  · intro a; simp [x1R, bits_0, bits_10, bits_110, bits_111]

lemma card_x0L : x0L.card = 3 := by rw [← length_sorted, sorted_x0L]; rfl
lemma card_x0R : x0R.card = 3 := by rw [← length_sorted, sorted_x0R]; rfl
lemma card_x1L : x1L.card = 4 := by rw [← length_sorted, sorted_x1L]; rfl
lemma card_x1R : x1R.card = 4 := by rw [← length_sorted, sorted_x1R]; rfl

lemma treeDiagram_x0 : IsTreeDiagram x0L x0R :=
  ⟨isTree_x0L, isTree_x0R, by rw [card_x0L, card_x0R]⟩
lemma treeDiagram_x1 : IsTreeDiagram x1L x1R :=
  ⟨isTree_x1L, isTree_x1R, by rw [card_x1L, card_x1R]⟩

lemma symm_apply_eq_of {e : UI ≃o UI} (x : UI) (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (h : (e ⟨y, hy⟩ : ℝ) = x) : (e.symm x : ℝ) = y := by
  have : e ⟨y, hy⟩ = x := Subtype.ext h
  rw [← this, OrderIso.symm_apply_apply]

/-- `(x0L, x0R)` describes `A⁻¹`. -/
lemma describes_x0_mapA : Describes x0L x0R mapA.symm := by
  refine ⟨treeDiagram_x0, ?_⟩
  rw [sorted_x0L, sorted_x0R]
  intro i hL hR x h1 h2
  rcases i with _ | _ | _ | i
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith⟩
    simp only [mapA, restrict_coe, lineA_apply]
    rw [aFun_of_mem1 (by linarith [x.2.1]) (by linarith)]; ring
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith⟩
    simp only [mapA, restrict_coe, lineA_apply]
    rw [aFun_of_mem2 (by linarith) (by linarith)]; ring
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith [x.2.2]⟩
    simp only [mapA, restrict_coe, lineA_apply]
    rw [aFun_of_mem3 (by linarith) (by linarith [x.2.2])]; ring
  · exfalso; simp at hL; omega

/-- `(x1L, x1R)` describes `B⁻¹`. -/
lemma describes_x1_mapB : Describes x1L x1R mapB.symm := by
  refine ⟨treeDiagram_x1, ?_⟩
  rw [sorted_x1L, sorted_x1R]
  intro i hL hR x h1 h2
  rcases i with _ | _ | _ | _ | i
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith⟩
    simp only [mapB, restrict_coe, lineB_apply]
    rw [bFun_of_le_half (by linarith)]
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith⟩
    simp only [mapB, restrict_coe, lineB_apply]
    rw [bFun_of_mem1 (by linarith) (by linarith)]; ring
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith⟩
    simp only [mapB, restrict_coe, lineB_apply]
    rw [bFun_of_mem2 (by linarith) (by linarith)]; ring
  · simp [seqVal_cons, seqVal_nil] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    apply symm_apply_eq_of x _ ⟨by linarith [x.2.1], by linarith [x.2.2]⟩
    simp only [mapB, restrict_coe, lineB_apply]
    rw [bFun_of_mem3 (by linarith) (by linarith [x.2.2])]; ring
  · exfalso; simp at hL; omega

lemma mapA_mem_F : mapA ∈ F := by
  rw [← closure_mapA_mapB_eq_F]; exact Subgroup.subset_closure (by simp)

lemma mapB_mem_F : mapB ∈ F := by
  rw [← closure_mapA_mapB_eq_F]; exact Subgroup.subset_closure (by simp)

/-- When some element of `F` is described by `(L, R)`, the epsilon choice in `ofDiagram` is. -/
lemma describes_toMap_ofDiagram {L R : Finset Seq} (h : ∃ f : F, Describes L R (f : UI ≃o UI)) :
    Describes L R (toMap (ofDiagram L R)) :=
  Classical.epsilon_spec (p := fun f : F => Describes L R (f : UI ≃o UI)) h

lemma toMap_x0 : toMap x0 = mapA.symm :=
  eq_of_describes (describes_toMap_ofDiagram ⟨⟨mapA⁻¹, F.inv_mem mapA_mem_F⟩, describes_x0_mapA⟩)
    describes_x0_mapA

lemma toMap_x1 : toMap x1 = mapB.symm :=
  eq_of_describes (describes_toMap_ofDiagram ⟨⟨mapB⁻¹, F.inv_mem mapB_mem_F⟩, describes_x1_mapB⟩)
    describes_x1_mapB

lemma op_mapA (hg : mapA ∈ F) : MulOpposite.op (⟨mapA, hg⟩ : F) = x0⁻¹ := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_inv]
  apply Subtype.ext
  change mapA = (toMap x0)⁻¹
  rw [toMap_x0]; rfl

lemma op_mapB (hg : mapB ∈ F) : MulOpposite.op (⟨mapB, hg⟩ : F) = x1⁻¹ := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_inv]
  apply Subtype.ext
  change mapB = (toMap x1)⁻¹
  rw [toMap_x1]; rfl

end MooreFoelner.Dev.Gen

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner CannonFloydParry MooreFoelner.Dev.Diagrams in
open Classical CannonFloydParry in
open Dev.Gen in
theorem solution : Subgroup.closure ({x0, x1} : Set MooreF) = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  obtain ⟨⟨g, hg⟩, rfl⟩ := MulOpposite.op_surjective f
  have hg' : g ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [closure_mapA_mapB_eq_F]; exact hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [op_mapA]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [op_mapB]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have hxF : x ∈ F := by rw [← closure_mapA_mapB_eq_F]; exact hx
    have hyF : y ∈ F := by rw [← closure_mapA_mapB_eq_F]; exact hy
    have : MulOpposite.op (⟨x * y, hg⟩ : F) =
        MulOpposite.op (⟨y, hyF⟩ : F) * MulOpposite.op (⟨x, hxF⟩ : F) := rfl
    rw [this]; exact Subgroup.mul_mem _ (ihy hyF) (ihx hxF)
  | inv x hx ihx =>
    have hxF : x ∈ F := by rw [← closure_mapA_mapB_eq_F]; exact hx
    have : MulOpposite.op (⟨x⁻¹, hg⟩ : F) = (MulOpposite.op (⟨x, hxF⟩ : F))⁻¹ := rfl
    rw [this]; exact Subgroup.inv_mem _ (ihx hxF)
