-- Prove2me | solution 1 for MITMSynthesis.mitm_factor_main
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T15:56:03.862735+00:00
-- url     : https://prove2.me/submissions/f9710ffe-58b6-40ad-94cc-ff060cff48ca

import Definitions.Def_MITMSynthesis_S
import Mathlib.Data.Set.Card
import Definitions.Def_MITMSynthesis_sortC
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Definitions.Def_MITMSynthesis_searchC
import Init.Data.Array.Lemmas
import Definitions.Def_MITMSynthesis_mitmFactor
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_MITMSynthesis_depthOneSet
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set

set_option autoImplicit false
noncomputable section

/- Inlined helper source: P089_SortGate.lean -/

/-!
S12 focused sort gate. Draft against the exact published Timed/mergeC/sortC bodies.
No compilation result is claimed by this file alone. The empty list is kept
separate because its charged cost is one. The bound is deliberately uniform in
the comparison keys and permits duplicate keys.
-/


namespace Prove2Me.S12.MITM

open MITMSynthesis

variable {α β κ : Type} [LinearOrder κ]

@[simp] theorem timed_pure_val (a : α) : (pure a : Timed α).val = a := rfl
@[simp] theorem timed_pure_cost (a : α) : (pure a : Timed α).cost = 0 := rfl
@[simp] theorem timed_bind_val (a : Timed α) (f : α → Timed β) :
    (a >>= f).val = (f a.val).val := rfl
@[simp] theorem timed_bind_cost (a : Timed α) (f : α → Timed β) :
    (a >>= f).cost = a.cost + (f a.val).cost := rfl

/-- The exact merge has the same result as the library merge with key comparison. -/
theorem merge_val (key : β → κ) (xs ys : List β) :
    (mergeC key xs ys).val = List.merge xs ys (fun a b => decide (key a ≤ key b)) := by
  match xs, ys with
  | [], ys => simp [mergeC, ticks]
  | x :: xs, [] => simp [mergeC, ticks]
  | x :: xs, y :: ys =>
    by_cases h : key x ≤ key y
    · have hc : compare (key x) (key y) ≠ .gt := compare_le_iff_le.mpr h
      simp [mergeC, cmpC, tick, List.merge, h, hc, merge_val key xs (y :: ys)]
    · have hc : compare (key x) (key y) = .gt :=
        compare_gt_iff_gt.mpr (lt_of_not_ge h)
      simp [mergeC, cmpC, tick, List.merge, h, hc, merge_val key (x :: xs) ys]
termination_by xs.length + ys.length
decreasing_by all_goals simp only [List.length_cons]; omega

theorem merge_perm (key : β → κ) (xs ys : List β) :
    (mergeC key xs ys).val.Perm (xs ++ ys) := by
  rw [merge_val]
  exact List.merge_perm_append _

theorem merge_pairwise (key : β → κ) (xs ys : List β)
    (hx : xs.Pairwise (fun a b => key a ≤ key b))
    (hy : ys.Pairwise (fun a b => key a ≤ key b)) :
    (mergeC key xs ys).val.Pairwise (fun a b => key a ≤ key b) := by
  rw [merge_val]
  letI : Std.Total (fun a b : β => key a ≤ key b) := ⟨fun a b => le_total _ _⟩
  letI : IsTrans β (fun a b : β => key a ≤ key b) := ⟨fun _ _ _ => le_trans⟩
  exact hx.merge hy

/-- A nonempty merge charges at most twice its total input length. -/
theorem merge_cost_le (key : β → κ) (xs ys : List β)
    (hne : 0 < xs.length + ys.length) :
    (mergeC key xs ys).cost ≤ 2 * (xs.length + ys.length) := by
  match xs, ys with
  | [], ys =>
    simp only [mergeC, timed_bind_cost, timed_bind_val, timed_pure_cost, ticks,
      Nat.add_zero, List.length_nil, Nat.zero_add] at *
    omega
  | x :: xs, [] =>
    simp only [mergeC, timed_bind_cost, timed_bind_val, timed_pure_cost, ticks,
      Nat.add_zero, List.length_nil, List.length_cons] at *
    omega
  | x :: xs, y :: ys =>
    by_cases hc : compare (key x) (key y) = .gt
    · have ih := merge_cost_le key (x :: xs) ys (by simp only [List.length_cons]; omega)
      simp only [mergeC, timed_bind_cost, timed_bind_val, timed_pure_cost,
        cmpC, tick, if_pos hc, Nat.add_zero]
      simp only [List.length_cons] at ih ⊢
      omega
    · have ih := merge_cost_le key xs (y :: ys) (by simp only [List.length_cons]; omega)
      simp only [mergeC, timed_bind_cost, timed_bind_val, timed_pure_cost,
        cmpC, tick, if_neg hc, Nat.add_zero]
      simp only [List.length_cons] at ih ⊢
      omega
termination_by xs.length + ys.length
decreasing_by all_goals simp only [List.length_cons]; omega

theorem sort_perm (key : β → κ) (l : List β) :
    (sortC key l).val.Perm l := by
  match l with
  | [] => simp [sortC, tick]
  | [x] => simp [sortC, tick]
  | x :: y :: zs =>
    simp only [sortC, timed_bind_val, ticks]
    apply (merge_perm key _ _).trans
    simpa only [List.take_append_drop] using
      (sort_perm key ((x :: y :: zs).take ((zs.length + 2) / 2))).append
        (sort_perm key ((x :: y :: zs).drop ((zs.length + 2) / 2)))
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

@[simp] theorem sort_length (key : β → κ) (l : List β) :
    (sortC key l).val.length = l.length := (sort_perm key l).length_eq

theorem sort_pairwise (key : β → κ) (l : List β) :
    (sortC key l).val.Pairwise (fun a b => key a ≤ key b) := by
  match l with
  | [] => simp [sortC, tick]
  | [x] => simp [sortC, tick]
  | x :: y :: zs =>
    simp only [sortC, timed_bind_val, ticks]
    exact merge_pairwise key _ _
      (sort_pairwise key ((x :: y :: zs).take ((zs.length + 2) / 2)))
      (sort_pairwise key ((x :: y :: zs).drop ((zs.length + 2) / 2)))
termination_by l.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

theorem sort_cost_nil (key : β → κ) : (sortC key []).cost = 1 := by
  simp [sortC, tick]

theorem sort_cost_step (key : β → κ) (x y : β) (zs : List β) :
    (sortC key (x :: y :: zs)).cost =
      (zs.length + 2) +
      (sortC key ((x :: y :: zs).take ((zs.length + 2) / 2))).cost +
      (sortC key ((x :: y :: zs).drop ((zs.length + 2) / 2))).cost +
      (mergeC key
        (sortC key ((x :: y :: zs).take ((zs.length + 2) / 2))).val
        (sortC key ((x :: y :: zs).drop ((zs.length + 2) / 2))).val).cost := by
  simp [sortC, ticks, Nat.add_assoc]

/-- A height-indexed bound on the actual charged cost, independent of key order. -/
theorem sort_cost_le_pow (key : β → κ) (k : ℕ) (l : List β)
    (hne : 0 < l.length) (hlen : l.length ≤ 2 ^ k) :
    (sortC key l).cost ≤ l.length * (3 * k + 1) := by
  induction k generalizing l with
  | zero =>
    have hl : l.length = 1 := by simp only [Nat.pow_zero] at hlen; omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
    simp [sortC, tick]
  | succ k ih =>
    match l with
    | [] => simp at hne
    | [x] => simp [sortC, tick]
    | x :: y :: zs =>
      let left := (x :: y :: zs).take ((zs.length + 2) / 2)
      let right := (x :: y :: zs).drop ((zs.length + 2) / 2)
      have hleft : 0 < left.length ∧ left.length ≤ 2 ^ k := by
        simp only [left, List.length_take, List.length_cons]
        simp only [List.length_cons, Nat.pow_succ] at hlen
        omega
      have hright : 0 < right.length ∧ right.length ≤ 2 ^ k := by
        simp only [right, List.length_drop, List.length_cons]
        simp only [List.length_cons, Nat.pow_succ] at hlen
        omega
      have hab : left.length + right.length = zs.length + 2 := by
        simp only [left, right, List.length_take, List.length_drop, List.length_cons]
        omega
      have ha := ih left hleft.1 hleft.2
      have hb := ih right hright.1 hright.2
      have hm := merge_cost_le key (sortC key left).val (sortC key right).val
        (by simp only [sort_length]; omega)
      simp only [sort_length, hab] at hm
      rw [sort_cost_step]
      change (zs.length + 2) + (sortC key left).cost + (sortC key right).cost +
        (mergeC key (sortC key left).val (sortC key right).val).cost ≤ _
      calc
        _ ≤ (zs.length + 2) + left.length * (3 * k + 1) +
            right.length * (3 * k + 1) + 2 * (zs.length + 2) := by omega
        _ = (zs.length + 2) + (left.length + right.length) * (3 * k + 1) +
            2 * (zs.length + 2) := by rw [Nat.add_mul]; omega
        _ = (zs.length + 2) * (3 * (k + 1) + 1) := by
          rw [hab]
          simp only [Nat.mul_add, Nat.add_mul]
          omega
        _ = _ := by simp only [List.length_cons]

theorem sort_cost_le_clog (key : β → κ) (l : List β) (hne : 0 < l.length) :
    (sortC key l).cost ≤ l.length * (3 * Nat.clog 2 l.length + 1) :=
  sort_cost_le_pow key (Nat.clog 2 l.length) l hne (Nat.le_pow_clog (by decide) _)

end Prove2Me.S12.MITM

/- Inlined helper source: P089_Search.lean -/


namespace Prove2Me.S12.MITM

open MITMSynthesis

variable {α β γ κ : Type} [LinearOrder κ]

@[simp] theorem search_pure_val (a : α) : (pure a : Timed α).val = a := rfl
@[simp] theorem search_pure_cost (a : α) : (pure a : Timed α).cost = 0 := rfl
@[simp] theorem search_bind_val (a : Timed α) (f : α → Timed β) :
    (a >>= f).val = (f a.val).val := rfl
@[simp] theorem search_bind_cost (a : Timed α) (f : α → Timed β) :
    (a >>= f).cost = a.cost + (f a.val).cost := rfl

theorem bsearch_val_step (key : β → κ) (arr : Array β) (q : κ) (lo hi : ℕ) :
    (bsearchC key arr q lo hi).val =
      if lo < hi then
        match arr[(lo + hi) / 2]? with
        | none => none
        | some b => match compare q (key b) with
          | .lt => (bsearchC key arr q lo ((lo + hi) / 2)).val
          | .gt => (bsearchC key arr q ((lo + hi) / 2 + 1) hi).val
          | .eq => some b
      else none := by
  rw [bsearchC]
  by_cases hw : lo < hi
  · simp only [dif_pos hw, if_pos hw]
    cases he : arr[(lo + hi) / 2]? with
    | none => simp [he, tick]
    | some b => cases hc : compare q (key b) <;> simp [he, cmpC, hc]
  · simp [hw, tick]

theorem bsearch_cost_step (key : β → κ) (arr : Array β) (q : κ) (lo hi : ℕ) :
    (bsearchC key arr q lo hi).cost =
      if lo < hi then
        match arr[(lo + hi) / 2]? with
        | none => 1
        | some b => match compare q (key b) with
          | .lt => 1 + (bsearchC key arr q lo ((lo + hi) / 2)).cost
          | .gt => 1 + (bsearchC key arr q ((lo + hi) / 2 + 1) hi).cost
          | .eq => 1
      else 1 := by
  rw [bsearchC]
  by_cases hw : lo < hi
  · simp only [dif_pos hw, if_pos hw]
    cases he : arr[(lo + hi) / 2]? with
    | none => simp [he, tick]
    | some b => cases hc : compare q (key b) <;> simp [he, cmpC, hc]
  · simp [hw, tick]

/-- Every successful search returns a genuine element of its original interval. -/
theorem bsearch_sound (key : β → κ) (arr : Array β) (q : κ) (lo hi : ℕ) (b : β)
    (hb : (bsearchC key arr q lo hi).val = some b) :
    ∃ i, lo ≤ i ∧ i < hi ∧ arr[i]? = some b ∧ key b = q := by
  rw [bsearch_val_step] at hb
  by_cases hw : lo < hi
  · rw [if_pos hw] at hb
    cases hm : arr[(lo + hi) / 2]? with
    | none => simp [hm] at hb
    | some a =>
      simp only [hm] at hb
      cases hc : compare q (key a) with
      | lt =>
        simp only [hc] at hb
        obtain ⟨i, hlo, hhi, he, hk⟩ := bsearch_sound key arr q lo ((lo + hi) / 2) b hb
        exact ⟨i, hlo, by omega, he, hk⟩
      | eq =>
        simp only [hc, Option.some.injEq] at hb
        subst b
        exact ⟨(lo + hi) / 2, by omega, by omega, hm, (compare_eq_iff_eq.mp hc).symm⟩
      | gt =>
        simp only [hc] at hb
        obtain ⟨i, hlo, hhi, he, hk⟩ :=
          bsearch_sound key arr q ((lo + hi) / 2 + 1) hi b hb
        exact ⟨i, by omega, hhi, he, hk⟩
  · simp [hw] at hb
termination_by hi - lo
decreasing_by all_goals omega

theorem array_key_mono (key : β → κ) (arr : Array β)
    (hs : arr.toList.Pairwise (fun a b => key a ≤ key b))
    {i j : ℕ} {a b : β} (hij : i ≤ j)
    (hi : arr[i]? = some a) (hj : arr[j]? = some b) : key a ≤ key b := by
  by_cases heq : i = j
  · subst j
    have hab : a = b := Option.some.inj (hi.symm.trans hj)
    simp [hab]
  · obtain ⟨his, hai⟩ := Array.getElem?_eq_some_iff.mp hi
    obtain ⟨hjs, hbj⟩ := Array.getElem?_eq_some_iff.mp hj
    have h := (List.pairwise_iff_getElem.mp hs) i j
      (by simpa using his) (by simpa using hjs) (by omega)
    simpa only [Array.getElem_toList, hai, hbj] using h

/-- Completeness uses only sortedness and the upper-bound validity of the interval. -/
theorem bsearch_complete (key : β → κ) (arr : Array β) (q : κ) (lo hi : ℕ)
    (hs : arr.toList.Pairwise (fun a b => key a ≤ key b)) (hsize : hi ≤ arr.size)
    (hwitness : ∃ i b, lo ≤ i ∧ i < hi ∧ arr[i]? = some b ∧ key b = q) :
    (bsearchC key arr q lo hi).val.isSome := by
  obtain ⟨i, b, hlo, hhi, hib, hbq⟩ := hwitness
  have hw : lo < hi := by omega
  have hmlo : lo ≤ (lo + hi) / 2 := by omega
  have hmhi : (lo + hi) / 2 < hi := by omega
  have hmsize : (lo + hi) / 2 < arr.size := lt_of_lt_of_le hmhi hsize
  let a := arr[(lo + hi) / 2]'hmsize
  have hma : arr[(lo + hi) / 2]? = some a := Array.getElem?_eq_getElem hmsize
  rw [bsearch_val_step, if_pos hw, hma]
  cases hc : compare q (key a) with
  | eq => simp [hc]
  | lt =>
    simp only [hc]
    have hqa : q < key a := compare_lt_iff_lt.mp hc
    have him : i < (lo + hi) / 2 := by
      by_contra hnot
      have hmono := array_key_mono key arr hs (show (lo + hi) / 2 ≤ i by omega) hma hib
      rw [hbq] at hmono
      exact (not_le_of_gt hqa) hmono
    exact bsearch_complete key arr q lo ((lo + hi) / 2) hs (by omega)
      ⟨i, b, hlo, him, hib, hbq⟩
  | gt =>
    simp only [hc]
    have haq : key a < q := compare_gt_iff_gt.mp hc
    have hmi : (lo + hi) / 2 < i := by
      by_contra hnot
      have hmono := array_key_mono key arr hs (show i ≤ (lo + hi) / 2 by omega) hib hma
      rw [hbq] at hmono
      exact (not_le_of_gt haq) hmono
    exact bsearch_complete key arr q ((lo + hi) / 2 + 1) hi hs hsize
      ⟨i, b, by omega, hhi, hib, hbq⟩
termination_by hi - lo
decreasing_by all_goals omega

theorem search_sound (key : β → κ) (arr : Array β) (q : κ) (b : β)
    (hb : (searchC key arr q).val = some b) : b ∈ arr ∧ key b = q := by
  obtain ⟨i, _, _, he, hk⟩ := bsearch_sound key arr q 0 arr.size b hb
  exact ⟨Array.mem_of_getElem? he, hk⟩

theorem search_isSome_iff (key : β → κ) (arr : Array β) (q : κ)
    (hs : arr.toList.Pairwise (fun a b => key a ≤ key b)) :
    (searchC key arr q).val.isSome ↔ ∃ b ∈ arr, key b = q := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
    exact ⟨b, search_sound key arr q b hb⟩
  · rintro ⟨b, hb, hk⟩
    obtain ⟨i, he⟩ := Array.getElem?_of_mem hb
    obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp he
    exact bsearch_complete key arr q 0 arr.size hs le_rfl ⟨i, b, Nat.zero_le _, hi, he, hk⟩

theorem bsearch_cost_le_pow (key : β → κ) (arr : Array β) (q : κ)
    (k lo hi : ℕ) (hlen : hi - lo < 2 ^ k) :
    (bsearchC key arr q lo hi).cost ≤ k + 1 := by
  induction k generalizing lo hi with
  | zero =>
    have hw : ¬lo < hi := by simp only [Nat.pow_zero] at hlen; omega
    rw [bsearch_cost_step, if_neg hw]
  | succ k ih =>
    rw [bsearch_cost_step]
    by_cases hw : lo < hi
    · rw [if_pos hw]
      cases hm : arr[(lo + hi) / 2]? with
      | none => simp
      | some b =>
        cases hc : compare q (key b) with
        | eq => simp [hc]
        | lt =>
          simp only [hc]
          have hleft : (lo + hi) / 2 - lo < 2 ^ k := by
            simp only [Nat.pow_succ] at hlen
            omega
          have hrec := ih lo ((lo + hi) / 2) hleft
          omega
        | gt =>
          simp only [hc]
          have hright : hi - ((lo + hi) / 2 + 1) < 2 ^ k := by
            simp only [Nat.pow_succ] at hlen
            omega
          have hrec := ih ((lo + hi) / 2 + 1) hi hright
          omega
    · rw [if_neg hw]
      omega

theorem search_cost_le (key : β → κ) (arr : Array β) (q : κ) :
    (searchC key arr q).cost ≤ Nat.clog 2 (arr.size + 1) + 1 := by
  apply bsearch_cost_le_pow
  have h := Nat.le_pow_clog (by decide : 1 < 2) (arr.size + 1)
  omega

theorem searchAll_sound (key : β → κ) (arr : Array β)
    (queries : List (κ × γ)) (c : γ) (b : β)
    (h : (searchAllC key arr queries).val = some (c, b)) :
    (key b, c) ∈ queries ∧ b ∈ arr := by
  induction queries with
  | nil => simp [searchAllC] at h
  | cons p queries ih =>
    rcases p with ⟨q, d⟩
    rw [searchAllC] at h
    simp only [search_bind_val, search_pure_val, tick] at h
    cases hs : (searchC key arr q).val with
    | none =>
      simp only [hs] at h
      obtain ⟨hmem, hb⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hmem, hb⟩
    | some a =>
      simp only [hs, search_pure_val, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      obtain ⟨ha, hk⟩ := search_sound key arr q _ hs
      exact ⟨by simp [hk], ha⟩

theorem searchAll_isSome_iff (key : β → κ) (arr : Array β)
    (queries : List (κ × γ))
    (hs : arr.toList.Pairwise (fun a b => key a ≤ key b)) :
    (searchAllC key arr queries).val.isSome ↔
      ∃ p ∈ queries, ∃ b ∈ arr, key b = p.1 := by
  induction queries with
  | nil => simp [searchAllC]
  | cons p queries ih =>
    rcases p with ⟨q, d⟩
    rw [searchAllC]
    simp only [search_bind_val, search_pure_val, tick]
    cases hsearch : (searchC key arr q).val with
    | none =>
      have hnot : ¬∃ b ∈ arr, key b = q := by
        intro h
        have hsome := (search_isSome_iff key arr q hs).mpr h
        simp [hsearch] at hsome
      simp [hsearch, ih, List.mem_cons, hnot]
    | some b =>
      obtain ⟨hb, hk⟩ := search_sound key arr q b hsearch
      simp only [hsearch, search_pure_val, Option.isSome_some, Bool.true_eq, true_iff]
      exact ⟨(q, d), List.mem_cons_self, b, hb, hk⟩

theorem searchAll_cost_le (key : β → κ) (arr : Array β) (queries : List (κ × γ)) :
    (searchAllC key arr queries).cost ≤
      queries.length * (Nat.clog 2 (arr.size + 1) + 2) := by
  induction queries with
  | nil => simp [searchAllC]
  | cons p queries ih =>
    rcases p with ⟨q, d⟩
    rw [searchAllC]
    simp only [search_bind_cost, search_bind_val, search_pure_cost, tick]
    have hc := search_cost_le key arr q
    cases hs : (searchC key arr q).val with
    | none =>
      simp only [hs, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    | some b =>
      simp only [hs, search_pure_cost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Prove2Me.S12.MITM


/- Inlined helper source: P089_Generation.lean -/

/-!
Exact corrected-interface generation lemmas for P089. No old theorem stubs.
The source remains a draft until accompanied by a successful Lean check.
-/


namespace Prove2Me.S12.MITM

open MITMSynthesis

variable {α β M : Type}

@[simp] theorem gen_pure_val (a : α) : (pure a : Timed α).val = a := rfl
@[simp] theorem gen_pure_cost (a : α) : (pure a : Timed α).cost = 0 := rfl
@[simp] theorem gen_bind_val (a : Timed α) (f : α → Timed β) :
    (a >>= f).val = (f a.val).val := rfl
@[simp] theorem gen_bind_cost (a : Timed α) (f : α → Timed β) :
    (a >>= f).cost = a.cost + (f a.val).cost := rfl

theorem gen_extendOne_val [Mul M] (W : M) (c : List α) (vs : List (α × M)) :
    (extendOneC W c vs).val = vs.map (fun p => (p.2 * W, p.1 :: c)) := by
  induction vs with
  | nil => simp [extendOneC]
  | cons p vs ih =>
    rcases p with ⟨a, v⟩
    simp [extendOneC, mulC, tick, ih]

theorem gen_extendOne_length [Mul M] (W : M) (c : List α) (vs : List (α × M)) :
    (extendOneC W c vs).val.length = vs.length := by
  rw [gen_extendOne_val, List.length_map]

theorem gen_extendOne_cost [Mul M] (W : M) (c : List α) (vs : List (α × M)) :
    (extendOneC W c vs).cost = 2 * vs.length := by
  induction vs with
  | nil => simp [extendOneC]
  | cons p vs ih =>
    rcases p with ⟨a, v⟩
    simp only [extendOneC, gen_bind_cost, gen_bind_val, gen_pure_cost, mulC, tick,
      ih, List.length_cons]
    omega

theorem gen_extend_val [Mul M] (vs : List (α × M)) (prev : List (M × List α)) :
    (extendC vs prev).val =
      prev.flatMap (fun p => vs.map (fun q => (q.2 * p.1, q.1 :: p.2))) := by
  induction prev with
  | nil => simp [extendC]
  | cons p prev ih =>
    rcases p with ⟨W, c⟩
    simp [extendC, ticks, gen_extendOne_val, ih]

theorem gen_extend_length [Mul M] (vs : List (α × M)) (prev : List (M × List α)) :
    (extendC vs prev).val.length = vs.length * prev.length := by
  induction prev with
  | nil => simp [extendC]
  | cons p prev ih =>
    rcases p with ⟨W, c⟩
    simp [extendC, ticks, gen_extendOne_length, ih, Nat.mul_add, Nat.add_comm]

theorem gen_extend_cost [Mul M] (vs : List (α × M)) (prev : List (M × List α)) :
    (extendC vs prev).cost = prev.length * (3 * vs.length + 1) := by
  induction prev with
  | nil => simp [extendC]
  | cons p prev ih =>
    rcases p with ⟨W, c⟩
    simp only [extendC, gen_bind_cost, gen_bind_val, gen_pure_cost, ticks,
      gen_extendOne_cost, gen_extendOne_length, ih, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

theorem gen_extend_mem_iff [Mul M] (vs : List (α × M)) (prev : List (M × List α))
    (W : M) (c : List α) :
    (W, c) ∈ (extendC vs prev).val ↔
      ∃ p ∈ prev, ∃ q ∈ vs, (q.2 * p.1, q.1 :: p.2) = (W, c) := by
  rw [gen_extend_val]
  simp only [List.mem_flatMap, List.mem_map]

theorem gen_queries_val [Mul M] [Star M] (U : M) (xs : List (M × List α)) :
    (queriesC U xs).val = xs.map (fun p => (star p.1 * U, p.2)) := by
  induction xs with
  | nil => simp [queriesC]
  | cons p xs ih =>
    rcases p with ⟨V, c⟩
    simp [queriesC, starC, mulC, tick, ih]

theorem gen_queries_length [Mul M] [Star M] (U : M) (xs : List (M × List α)) :
    (queriesC U xs).val.length = xs.length := by
  rw [gen_queries_val, List.length_map]

theorem gen_queries_cost [Mul M] [Star M] (U : M) (xs : List (M × List α)) :
    (queriesC U xs).cost = 3 * xs.length := by
  induction xs with
  | nil => simp [queriesC]
  | cons p xs ih =>
    rcases p with ⟨V, c⟩
    simp only [queriesC, gen_bind_cost, gen_bind_val, gen_pure_cost, starC, mulC,
      tick, ih, List.length_cons]
    omega

theorem gen_queries_mem_iff [Mul M] [Star M] (U W : M) (xs : List (M × List α))
    (c : List α) :
    (W, c) ∈ (queriesC U xs).val ↔ ∃ V, (V, c) ∈ xs ∧ star V * U = W := by
  rw [gen_queries_val]
  constructor
  · intro h
    obtain ⟨⟨V, d⟩, hmem, heq⟩ := List.mem_map.mp h
    have he := Prod.mk.inj heq
    dsimp at he
    rcases he with ⟨hW, hd⟩
    subst d
    exact ⟨V, hmem, hW⟩
  · rintro ⟨V, hmem, heq⟩
    exact List.mem_map.mpr ⟨(V, c), hmem, by simp only [heq]⟩

theorem gen_buildS_val_zero [Monoid M] (vs : List (α × M)) :
    (buildS vs 0).val = [(1, [])] := rfl

theorem gen_buildS_val_succ [Monoid M] (vs : List (α × M)) (i : ℕ) :
    (buildS vs (i + 1)).val = (extendC vs (buildS vs i).val).val := rfl

theorem gen_buildS_length [Monoid M] (vs : List (α × M)) (i : ℕ) :
    (buildS vs i).val.length = vs.length ^ i := by
  induction i with
  | zero => simp [gen_buildS_val_zero]
  | succ i ih =>
    rw [gen_buildS_val_succ, gen_extend_length, ih, pow_succ]
    exact Nat.mul_comm _ _

theorem gen_buildS_cost_zero [Monoid M] (vs : List (α × M)) :
    (buildS vs 0).cost = 1 := rfl

theorem gen_buildS_cost_succ [Monoid M] (vs : List (α × M)) (i : ℕ) :
    (buildS vs (i + 1)).cost = (buildS vs i).cost +
      (buildS vs i).val.length * (3 * vs.length + 1) := by
  simp only [buildS, gen_bind_cost, gen_extend_cost]

theorem gen_buildS_cost [Monoid M] (vs : List (α × M)) (i : ℕ) :
    (buildS vs i).cost =
      1 + (3 * vs.length + 1) * ∑ j ∈ Finset.range i, vs.length ^ j := by
  induction i with
  | zero => simp [gen_buildS_cost_zero]
  | succ i ih =>
    rw [gen_buildS_cost_succ, ih, gen_buildS_length, Finset.sum_range_succ]
    rw [Nat.mul_comm (vs.length ^ i) (3 * vs.length + 1)]
    rw [Nat.mul_add]
    exact Nat.add_assoc _ _ _

/-- Exact circuit characterization for a consistent interpretation of labels.
No distinctness or inverse-closure assumption is needed. -/
theorem gen_buildS_mem_iff [Monoid M] (vs : List (α × M)) (f : α → M)
    (hvs : ∀ p ∈ vs, f p.1 = p.2) (i : ℕ) (W : M) (c : List α) :
    (W, c) ∈ (buildS vs i).val ↔
      c.length = i ∧ (∀ a ∈ c, (a, f a) ∈ vs) ∧ (c.map f).prod = W := by
  induction i generalizing W c with
  | zero =>
    constructor
    · intro h
      have hp : (W, c) = (1, []) := by simpa only [gen_buildS_val_zero, List.mem_singleton] using h
      have he := Prod.mk.inj hp
      rcases he with ⟨rfl, rfl⟩
      simp
    · rintro ⟨hlen, _, hprod⟩
      have hc : c = [] := List.eq_nil_of_length_eq_zero hlen
      subst c
      have hW : W = 1 := by simpa using hprod.symm
      subst W
      simp [gen_buildS_val_zero]
  | succ i ih =>
    rw [gen_buildS_val_succ, gen_extend_mem_iff]
    constructor
    · rintro ⟨⟨V, d⟩, hprev, ⟨a, v⟩, hav, heq⟩
      have he := Prod.mk.inj heq
      dsimp at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨hlen, hall, hprod⟩ := (ih V d).mp hprev
      have havf : f a = v := hvs (a, v) hav
      refine ⟨by simp [hlen], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa only [havf] using hav
        · exact hall x hx
      · simp only [List.map_cons, List.prod_cons, havf, hprod]
    · rintro ⟨hlen, hall, hprod⟩
      cases c with
      | nil => simp at hlen
      | cons a c =>
        have hlen' : c.length = i := by simpa only [List.length_cons] using Nat.succ.inj hlen
        have hprev : ((c.map f).prod, c) ∈ (buildS vs i).val :=
          (ih _ _).mpr ⟨hlen', fun x hx => hall x (List.mem_cons_of_mem a hx), rfl⟩
        refine ⟨((c.map f).prod, c), hprev, (a, f a), hall a List.mem_cons_self, ?_⟩
        apply Prod.ext
        · simpa only [List.map_cons, List.prod_cons] using hprod
        · rfl

theorem gen_buildS_circuit_spec [Monoid M] (vs : List (α × M)) (f : α → M)
    (Good : α → Prop) (hvs : ∀ p ∈ vs, Good p.1 ∧ f p.1 = p.2)
    (i : ℕ) (W : M) (c : List α) (hmem : (W, c) ∈ (buildS vs i).val) :
    c.length = i ∧ (∀ a ∈ c, Good a) ∧ (c.map f).prod = W := by
  obtain ⟨hlen, hall, hprod⟩ :=
    (gen_buildS_mem_iff vs f (fun p hp => (hvs p hp).2) i W c).mp hmem
  exact ⟨hlen, fun a ha => (hvs (a, f a) (hall a ha)).1, hprod⟩

/-- Value completeness without a deterministic label interpretation. The right
side is the exact word-product definition of `S` for the enumerated values. -/
theorem gen_buildS_value_iff [Monoid M] (vs : List (α × M)) (i : ℕ) (W : M) :
    (∃ c, (W, c) ∈ (buildS vs i).val) ↔
      ∃ values : List M, values.length = i ∧
        (∀ v ∈ values, ∃ a, (a, v) ∈ vs) ∧ values.prod = W := by
  induction i generalizing W with
  | zero =>
    constructor
    · rintro ⟨c, hc⟩
      have hp : (W, c) = (1, []) := by
        simpa only [gen_buildS_val_zero, List.mem_singleton] using hc
      have hW : W = 1 := congrArg Prod.fst hp
      exact ⟨[], rfl, by simp, hW.symm⟩
    · rintro ⟨values, hlen, _, hprod⟩
      have hv : values = [] := List.eq_nil_of_length_eq_zero hlen
      subst values
      have hW : W = 1 := by simpa using hprod.symm
      subst W
      exact ⟨[], by simp [gen_buildS_val_zero]⟩
  | succ i ih =>
    constructor
    · rintro ⟨c, hc⟩
      rw [gen_buildS_val_succ, gen_extend_mem_iff] at hc
      obtain ⟨⟨V, d⟩, hV, ⟨a, v⟩, hav, heq⟩ := hc
      have hW : v * V = W := congrArg Prod.fst heq
      obtain ⟨values, hlen, hall, hprod⟩ := (ih V).mp ⟨d, hV⟩
      refine ⟨v :: values, by simp [hlen], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a, hav⟩
        · exact hall x hx
      · simpa only [List.prod_cons, hprod] using hW
    · rintro ⟨values, hlen, hall, hprod⟩
      cases values with
      | nil => simp at hlen
      | cons v values =>
        have hlen' : values.length = i := Nat.succ.inj hlen
        obtain ⟨a, hav⟩ := hall v List.mem_cons_self
        obtain ⟨c, hc⟩ := (ih values.prod).mpr
          ⟨values, hlen', fun x hx => hall x (List.mem_cons_of_mem v hx), rfl⟩
        refine ⟨a :: c, ?_⟩
        rw [gen_buildS_val_succ, gen_extend_mem_iff]
        refine ⟨(values.prod, c), hc, (a, v), hav, ?_⟩
        apply Prod.ext
        · simpa only [List.prod_cons] using hprod
        · rfl

/-- The generated matrices stay in every submonoid containing the supplied
layers. Taking the unitary submonoid gives the needed unitary preservation. -/
theorem gen_extend_mem_submonoid [Monoid M] (K : Submonoid M)
    (vs : List (α × M)) (prev : List (M × List α))
    (hvs : ∀ p ∈ vs, p.2 ∈ K) (hprev : ∀ p ∈ prev, p.1 ∈ K)
    (W : M) (c : List α) (hmem : (W, c) ∈ (extendC vs prev).val) : W ∈ K := by
  obtain ⟨p, hp, q, hq, heq⟩ := (gen_extend_mem_iff vs prev W c).mp hmem
  have hfst := congrArg Prod.fst heq
  dsimp at hfst
  rw [← hfst]
  exact K.mul_mem (hvs q hq) (hprev p hp)

theorem gen_buildS_mem_submonoid [Monoid M] (K : Submonoid M)
    (vs : List (α × M)) (hvs : ∀ p ∈ vs, p.2 ∈ K)
    (i : ℕ) (W : M) (c : List α) (hmem : (W, c) ∈ (buildS vs i).val) : W ∈ K := by
  induction i generalizing W c with
  | zero =>
    have hp : (W, c) = (1, []) := by simpa only [gen_buildS_val_zero, List.mem_singleton] using hmem
    have hW : W = 1 := congrArg Prod.fst hp
    rw [hW]
    exact K.one_mem
  | succ i ih =>
    rw [gen_buildS_val_succ] at hmem
    exact gen_extend_mem_submonoid K vs (buildS vs i).val hvs
      (fun p hp => ih p.1 p.2 hp) W c hmem

end Prove2Me.S12.MITM


/- Inlined helper source: P089_Loop_body.lean -/
/-! Corrected P089 value/loop layer. Append after the checked sorting,
search, and generation helper declarations. No older theorem stubs are used. -/

namespace Prove2Me.S12.MITM

open MITMSynthesis

variable {α β M κ : Type} [Monoid M] [Star M] [LinearOrder M]

theorem iter_inr_eq (vs : List (α × M)) (U : M) (l i : ℕ)
    (prev cur : List (M × List α)) (h : (iterC vs U l i prev).val = .inr cur) :
    cur = (extendC vs prev).val := by
  simp only [iterC, search_bind_val, search_pure_val, tick, ticks] at h
  split at h
  · simp_all
  · split at h
    · simp only [search_bind_val, search_pure_val, tick, ticks] at h
      split at h <;> simp_all
    · simpa using h.symm

def GeneratedAt (vs : List (α × M)) (i : ℕ) (U : M) : Prop :=
  ∃ c, (U, c) ∈ (buildS vs i).val

theorem generated_mul (vs : List (α × M)) (a b : ℕ) (V W : M)
    (hV : GeneratedAt vs a V) (hW : GeneratedAt vs b W) :
    GeneratedAt vs (a + b) (V * W) := by
  obtain ⟨L, hLlen, hLmem, hLprod⟩ := (gen_buildS_value_iff vs a V).mp hV
  obtain ⟨R, hRlen, hRmem, hRprod⟩ := (gen_buildS_value_iff vs b W).mp hW
  apply (gen_buildS_value_iff vs (a + b) (V * W)).mpr
  refine ⟨L ++ R, by simp [hLlen, hRlen], ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hLmem v hv
    · exact hRmem v hv
  · rw [List.prod_append, hLprod, hRprod]

theorem generated_collision_iff (vs : List (α × M))
    (hunit : ∀ i V c, (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1)
    (a b : ℕ) (U : M) :
    (∃ V c W d, (V, c) ∈ (buildS vs a).val ∧
      (W, d) ∈ (buildS vs b).val ∧ star V * U = W) ↔
      GeneratedAt vs (a + b) U := by
  constructor
  · rintro ⟨V, c, W, d, hV, hW, heq⟩
    have hprod : V * W = U := by
      rw [← heq, ← mul_assoc, (hunit a V c hV).2, one_mul]
    rw [← hprod]
    exact generated_mul vs a b V W ⟨c, hV⟩ ⟨d, hW⟩
  · intro hU
    obtain ⟨L, hlen, hmem, hprod⟩ := (gen_buildS_value_iff vs (a + b) U).mp hU
    have hV : GeneratedAt vs a (L.take a).prod := by
      apply (gen_buildS_value_iff vs a (L.take a).prod).mpr
      refine ⟨L.take a, ?_, ?_, rfl⟩
      · simp only [List.length_take, hlen]
        omega
      · intro v hv
        exact hmem v (List.mem_of_mem_take hv)
    have hW : GeneratedAt vs b (L.drop a).prod := by
      apply (gen_buildS_value_iff vs b (L.drop a).prod).mpr
      refine ⟨L.drop a, ?_, ?_, rfl⟩
      · simp only [List.length_drop, hlen]
        omega
      · intro v hv
        exact hmem v (List.mem_of_mem_drop hv)
    obtain ⟨c, hc⟩ := hV
    obtain ⟨d, hd⟩ := hW
    refine ⟨(L.take a).prod, c, (L.drop a).prod, d, hc, hd, ?_⟩
    have hsplit : (L.take a).prod * (L.drop a).prod = U := by
      rw [← List.prod_append, List.take_append_drop]
      exact hprod
    rw [← hsplit, ← mul_assoc, (hunit a _ c hc).1, one_mul]

theorem sorted_array_mem_iff [LinearOrder κ] (key : β → κ) (xs : List β) (b : β) :
    b ∈ (sortC key xs).val.toArray ↔ b ∈ xs := by
  simpa using (sort_perm key xs).mem_iff (a := b)

theorem generated_search_sound (vs : List (α × M)) (U : M) (a b : ℕ)
    (c : List α) (W : M) (d : List α)
    (h : (searchAllC Prod.fst (sortC Prod.fst (buildS vs b).val).val.toArray
      (queriesC U (buildS vs a).val).val).val = some (c, (W, d))) :
    ∃ V, (V, c) ∈ (buildS vs a).val ∧ (W, d) ∈ (buildS vs b).val ∧ star V * U = W := by
  obtain ⟨hq, hw⟩ := searchAll_sound Prod.fst _ _ c (W, d) h
  obtain ⟨V, hV, heq⟩ := (gen_queries_mem_iff U W (buildS vs a).val c).mp hq
  exact ⟨V, hV, (sorted_array_mem_iff Prod.fst _ (W, d)).mp hw, heq⟩

theorem generated_search_isSome_iff (vs : List (α × M))
    (hunit : ∀ i V c, (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1)
    (U : M) (a b : ℕ) :
    (searchAllC Prod.fst (sortC Prod.fst (buildS vs b).val).val.toArray
      (queriesC U (buildS vs a).val).val).val.isSome ↔ GeneratedAt vs (a + b) U := by
  rw [searchAll_isSome_iff _ _ _ (by simpa using sort_pairwise Prod.fst (buildS vs b).val)]
  rw [← generated_collision_iff vs hunit a b U]
  constructor
  · rintro ⟨⟨q, c⟩, hq, ⟨W, d⟩, hw, hk⟩
    obtain ⟨V, hV, heq⟩ := (gen_queries_mem_iff U q (buildS vs a).val c).mp hq
    exact ⟨V, c, W, d, hV, (sorted_array_mem_iff Prod.fst _ (W, d)).mp hw,
      heq.trans hk.symm⟩
  · rintro ⟨V, c, W, d, hV, hW, heq⟩
    refine ⟨(W, c), ?_, (W, d), ?_, rfl⟩
    · exact (gen_queries_mem_iff U W (buildS vs a).val c).mpr ⟨V, hV, heq⟩
    · exact (sorted_array_mem_iff Prod.fst _ (W, d)).mpr hW

theorem generated_append_mem (vs : List (α × M)) (f : α → M)
    (hvs : ∀ p ∈ vs, f p.1 = p.2) (a b : ℕ) (V W : M) (c d : List α)
    (hc : (V, c) ∈ (buildS vs a).val) (hd : (W, d) ∈ (buildS vs b).val) :
    (V * W, c ++ d) ∈ (buildS vs (a + b)).val := by
  obtain ⟨hcLen, hcMem, hcProd⟩ := (gen_buildS_mem_iff vs f hvs a V c).mp hc
  obtain ⟨hdLen, hdMem, hdProd⟩ := (gen_buildS_mem_iff vs f hvs b W d).mp hd
  apply (gen_buildS_mem_iff vs f hvs (a + b) (V * W) (c ++ d)).mpr
  refine ⟨by simp [hcLen, hdLen], ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hcMem x hx
    · exact hdMem x hx
  · rw [List.map_append, List.prod_append, hcProd, hdProd]

theorem generated_search_result_mem (vs : List (α × M)) (f : α → M)
    (hvs : ∀ p ∈ vs, f p.1 = p.2)
    (hunit : ∀ i V c, (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1)
    (U : M) (a b : ℕ) (c : List α) (W : M) (d : List α)
    (h : (searchAllC Prod.fst (sortC Prod.fst (buildS vs b).val).val.toArray
      (queriesC U (buildS vs a).val).val).val = some (c, (W, d))) :
    (U, c ++ d) ∈ (buildS vs (a + b)).val := by
  obtain ⟨V, hV, hW, heq⟩ := generated_search_sound vs U a b c W d h
  have hprod : V * W = U := by
    rw [← heq, ← mul_assoc, (hunit a V c hV).2, one_mul]
  rw [← hprod]
  exact generated_append_mem vs f hvs a b V W c d hV hW

/-- The odd test is preferred; the even test is present only within the bound. -/
theorem iter_value_spec (vs : List (α × M)) (f : α → M)
    (hvs : ∀ p ∈ vs, f p.1 = p.2)
    (hunit : ∀ i V c, (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1)
    (U : M) (l i : ℕ) :
    match (iterC vs U l (i + 1) (buildS vs i).val).val with
    | .inl c =>
        (U, c) ∈ (buildS vs (2 * i + 1)).val ∨
          (2 * (i + 1) ≤ l ∧ ¬ GeneratedAt vs (2 * i + 1) U ∧
            (U, c) ∈ (buildS vs (2 * (i + 1))).val)
    | .inr cur =>
        cur = (buildS vs (i + 1)).val ∧ ¬ GeneratedAt vs (2 * i + 1) U ∧
          (2 * (i + 1) ≤ l → ¬ GeneratedAt vs (2 * (i + 1)) U) := by
  have hodd : i + (i + 1) = 2 * i + 1 := by omega
  have heven : (i + 1) + (i + 1) = 2 * (i + 1) := by omega
  have odd_iff := generated_search_isSome_iff vs hunit U i (i + 1)
  have even_iff := generated_search_isSome_iff vs hunit U (i + 1) (i + 1)
  rw [hodd] at odd_iff
  rw [heven] at even_iff
  simp only [iterC, search_bind_val, search_pure_val, tick, ticks,
    ← gen_buildS_val_succ]
  cases h1 : (searchAllC Prod.fst (sortC Prod.fst (buildS vs (i + 1)).val).val.toArray
      (queriesC U (buildS vs i).val).val).val with
  | some p =>
    rcases p with ⟨c, W, d⟩
    simp only [h1, search_bind_val, search_pure_val, ticks]
    left
    simpa only [hodd] using generated_search_result_mem vs f hvs hunit U i (i + 1) c W d h1
  | none =>
    have noOdd : ¬ GeneratedAt vs (2 * i + 1) U := by
      intro hh
      have ht := odd_iff.mpr hh
      simp [h1] at ht
    by_cases hg : 2 * (i + 1) ≤ l
    · simp only [h1, if_pos hg, search_bind_val, search_pure_val]
      cases h2 : (searchAllC Prod.fst (sortC Prod.fst (buildS vs (i + 1)).val).val.toArray
          (queriesC U (buildS vs (i + 1)).val).val).val with
      | some p =>
        rcases p with ⟨c, W, d⟩
        simp only [h2, search_bind_val, search_pure_val, ticks]
        right
        refine ⟨hg, noOdd, ?_⟩
        simpa only [heven] using
          generated_search_result_mem vs f hvs hunit U (i + 1) (i + 1) c W d h2
      | none =>
        simp only [h2, search_pure_val]
        refine ⟨True.intro, noOdd, fun _ hh => ?_⟩
        have ht := even_iff.mpr hh
        simp [h2] at ht
    · simp only [h1, if_neg hg, search_pure_val]
      exact ⟨True.intro, noOdd, fun h => False.elim (hg h)⟩

/-- The remaining budget ends at the given bound, and earlier allowed depths failed. -/
theorem loop_value_correct (vs : List (α × M)) (f : α → M)
    (hvs : ∀ p ∈ vs, f p.1 = p.2)
    (hunit : ∀ i V c, (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1)
    (U : M) (l k i : ℕ)
    (hcover : l ≤ 2 * (i + k)) (hcap : 2 * (i + k) ≤ l + 1)
    (hprior : ∀ m, m ≤ 2 * i → m ≤ l → ¬ GeneratedAt vs m U) :
    ((loopC vs U l k (i + 1) (buildS vs i).val).val.isSome ↔
      ∃ m ≤ l, GeneratedAt vs m U) ∧
    (∀ c, (loopC vs U l k (i + 1) (buildS vs i).val).val = some c →
      c.length ≤ l ∧ (U, c) ∈ (buildS vs c.length).val ∧
        ∀ m, GeneratedAt vs m U → c.length ≤ m) := by
  induction k generalizing i with
  | zero =>
    constructor
    · constructor
      · intro h
        simp [loopC, tick] at h
      · rintro ⟨m, hml, hm⟩
        exact False.elim ((hprior m (by omega) hml) hm)
    · intro c hc
      simp [loopC, tick] at hc
  | succ k ih =>
    have hs := iter_value_spec vs f hvs hunit U l i
    cases hiter : (iterC vs U l (i + 1) (buildS vs i).val).val with
    | inl c =>
      simp only [hiter] at hs
      have hret : c.length ≤ l ∧ (U, c) ∈ (buildS vs c.length).val ∧
          ∀ m, GeneratedAt vs m U → c.length ≤ m := by
        rcases hs with hodd | ⟨hg, noOdd, heven⟩
        · have hlen := ((gen_buildS_mem_iff vs f hvs (2 * i + 1) U c).mp hodd).1
          refine ⟨by omega, ?_, ?_⟩
          · simpa only [hlen] using hodd
          · intro m hm
            by_contra hn
            exact (hprior m (by omega) (by omega)) hm
        · have hlen := ((gen_buildS_mem_iff vs f hvs (2 * (i + 1)) U c).mp heven).1
          refine ⟨by omega, ?_, ?_⟩
          · simpa only [hlen] using heven
          · intro m hm
            by_contra hn
            by_cases hmi : m ≤ 2 * i
            · exact (hprior m hmi (by omega)) hm
            · have heq : m = 2 * i + 1 := by omega
              subst m
              exact noOdd hm
      constructor
      · constructor
        · intro _
          exact ⟨c.length, hret.1, c, hret.2.1⟩
        · intro _
          simp [loopC, tick, hiter]
      · intro d hd
        have hcd : c = d := by
          simpa only [loopC, search_bind_val, search_pure_val, tick, hiter,
            Option.some.injEq] using hd
        subst d
        exact hret
    | inr cur =>
      simp only [hiter] at hs
      obtain ⟨hcur, noOdd, noEven⟩ := hs
      subst cur
      have hprior' : ∀ m, m ≤ 2 * (i + 1) → m ≤ l → ¬ GeneratedAt vs m U := by
        intro m hmi hml hm
        by_cases hold : m ≤ 2 * i
        · exact (hprior m hold hml) hm
        · have heq : m = 2 * i + 1 ∨ m = 2 * (i + 1) := by omega
          rcases heq with rfl | rfl
          · exact noOdd hm
          · exact (noEven hml) hm
      have hnext := ih (i + 1) (by omega) (by omega) hprior'
      simpa only [loopC, search_bind_val, search_pure_val, tick, hiter] using hnext

theorem mitm_val_step (vs : List (α × M)) (U : M) (l : ℕ) :
    (mitmFactor vs U l).val =
      if U = 1 then some [] else (loopC vs U l ((l + 1) / 2) 1 [(1, [])]).val := by
  rw [mitmFactor]
  simp only [search_bind_val, cmpC]
  by_cases he : U = 1
  · subst U
    simp
  · have hc : compare U 1 ≠ .eq := fun h => he (compare_eq_iff_eq.mp h)
    simp [he, hc]

/-- Correctness and minimum depth of the exact corrected algorithm, before the physical adapter. -/
theorem mitm_value_correct (vs : List (α × M)) (f : α → M)
    (hvs : ∀ p ∈ vs, f p.1 = p.2)
    (hunit : ∀ i V c, (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1)
    (U : M) (l : ℕ) :
    ((mitmFactor vs U l).val.isSome ↔ ∃ m ≤ l, GeneratedAt vs m U) ∧
    (∀ c, (mitmFactor vs U l).val = some c →
      c.length ≤ l ∧ (U, c) ∈ (buildS vs c.length).val ∧
        ∀ m, GeneratedAt vs m U → c.length ≤ m) := by
  by_cases he : U = 1
  · subst U
    simp only [mitm_val_step, if_pos rfl]
    constructor
    · constructor
      · intro _
        exact ⟨0, Nat.zero_le _, [], by simp [gen_buildS_val_zero]⟩
      · intro _
        rfl
    · intro c hc
      have hc' : c = [] := (Option.some.inj hc).symm
      subst c
      exact ⟨Nat.zero_le _, by simp [gen_buildS_val_zero], fun m _ => Nat.zero_le m⟩
  · have hprior : ∀ m, m ≤ 2 * 0 → m ≤ l → ¬ GeneratedAt vs m U := by
      intro m hm _ hgen
      have hm0 : m = 0 := by omega
      subst m
      obtain ⟨c, hc⟩ := hgen
      have hp : (U, c) = (1, []) := by simpa [gen_buildS_val_zero] using hc
      exact he (congrArg Prod.fst hp)
    have hloop := loop_value_correct vs f hvs hunit U l ((l + 1) / 2) 0
      (by omega) (by omega) hprior
    simpa only [mitm_val_step, if_neg he, gen_buildS_val_zero, Nat.zero_add,
      Nat.zero_mul] using hloop

end Prove2Me.S12.MITM


/- Inlined helper source: P089_CostSums.lean -/


open scoped BigOperators

namespace Prove2Me.S12.MITM

theorem scalar_index_le_pow (q r : ℕ) (hq : 2 ≤ q) :
    r + 2 ≤ q ^ (r + 1) := by
  induction r with
  | zero => simpa using hq
  | succ r ih =>
      calc
        r.succ + 2 ≤ (r + 2) * 2 := by omega
        _ ≤ q ^ (r + 1) * q := Nat.mul_le_mul ih hq
        _ = q ^ (r.succ + 1) := (pow_succ q (r + 1)).symm

theorem scalar_geom_shift_le (q r k : ℕ) (hq : 2 ≤ q) :
    (∑ j ∈ Finset.range k, q ^ (r + j + 1)) ≤ 2 * q ^ (r + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range k, q ^ (r + j + 1)) + q ^ (r + k + 1)
            ≤ 2 * q ^ (r + k) + q ^ (r + k + 1) := Nat.add_le_add_right ih _
        _ = (2 + q) * q ^ (r + k) := by rw [pow_succ]; ring
        _ ≤ (2 * q) * q ^ (r + k) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * q ^ (r + k.succ) := by rw [Nat.add_succ, pow_succ]; ring

theorem scalar_geom_le (q k : ℕ) (hq : 2 ≤ q) :
    (∑ j ∈ Finset.range k, q ^ (j + 1)) ≤ 2 * q ^ k := by
  simpa using scalar_geom_shift_le q 0 k hq

theorem scalar_weighted_geom_le (q k : ℕ) (hq : 2 ≤ q) :
    (∑ j ∈ Finset.range k, (j + 1) * q ^ (j + 1)) ≤ 2 * k * q ^ k := by
  calc
    (∑ j ∈ Finset.range k, (j + 1) * q ^ (j + 1))
        ≤ ∑ j ∈ Finset.range k, k * q ^ (j + 1) := by
          apply Finset.sum_le_sum
          intro j hj
          exact Nat.mul_le_mul_right _ (by have := Finset.mem_range.mp hj; omega)
    _ = k * (∑ j ∈ Finset.range k, q ^ (j + 1)) := by rw [Finset.mul_sum]
    _ ≤ k * (2 * q ^ k) := Nat.mul_le_mul_left _ (scalar_geom_le q k hq)
    _ = 2 * k * q ^ k := by ac_rfl

theorem scalar_stage_sum_le (A q r k : ℕ) (hq : 2 ≤ q) :
    (∑ j ∈ Finset.range k,
      A * q ^ (r + j + 1) * (Nat.clog 2 (q ^ (r + j + 1) + 1) + 1))
      ≤ (2 * A) * q ^ (r + k) * (Nat.clog 2 (q ^ (r + k) + 1) + 1) := by
  let L := Nat.clog 2 (q ^ (r + k) + 1) + 1
  have hmono (j : ℕ) (hj : j ∈ Finset.range k) :
      Nat.clog 2 (q ^ (r + j + 1) + 1) + 1 ≤ L := by
    have hp : q ^ (r + j + 1) ≤ q ^ (r + k) :=
      Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hj; omega)
    exact Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.add_le_add_right hp 1)) 1
  calc
    (∑ j ∈ Finset.range k,
      A * q ^ (r + j + 1) * (Nat.clog 2 (q ^ (r + j + 1) + 1) + 1))
        ≤ ∑ j ∈ Finset.range k, A * q ^ (r + j + 1) * L := by
          exact Finset.sum_le_sum fun j hj => Nat.mul_le_mul_left _ (hmono j hj)
    _ = A * (∑ j ∈ Finset.range k, q ^ (r + j + 1)) * L := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ A * (2 * q ^ (r + k)) * L :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (scalar_geom_shift_le q r k hq))
    _ = (2 * A) * q ^ (r + k) * (Nat.clog 2 (q ^ (r + k) + 1) + 1) := by
      dsimp [L]
      ac_rfl

theorem scalar_iter_cost (n t : ℕ) (hn : 1 ≤ n) :
    1 + 4 * n + n * (3 * t + 1) + (n + 1) + 3 * n + n * (t + 2) +
      3 * n + n * (t + 2) + n ≤ 20 * n * (t + 1) := by
  nlinarith [Nat.zero_le (n * t)]

theorem scalar_total_cost_le (q k : ℕ) (hq : 2 ≤ q) :
    2 + (∑ j ∈ Finset.range k,
      (20 * q ^ (j + 1) * (Nat.clog 2 (q ^ (j + 1) + 1) + 1) + 1))
      ≤ 50 * q ^ k * (Nat.clog 2 (q ^ k + 1) + 1) := by
  let L := Nat.clog 2 (q ^ k + 1) + 1
  have hs : (∑ j ∈ Finset.range k,
      20 * q ^ (j + 1) * (Nat.clog 2 (q ^ (j + 1) + 1) + 1))
      ≤ 40 * q ^ k * L := by
    simpa [L] using scalar_stage_sum_le 20 q 0 k hq
  have hd : k + 1 ≤ q ^ k := by
    cases k with
    | zero => simp
    | succ r =>
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using scalar_index_le_pow q r hq
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hp : q ^ k ≤ q ^ k * L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (q ^ k) hL
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
  change 2 + ((∑ j ∈ Finset.range k,
      20 * q ^ (j + 1) * (Nat.clog 2 (q ^ (j + 1) + 1) + 1)) + k)
      ≤ 50 * q ^ k * L
  nlinarith

theorem scalar_clog_succ_le (N : ℕ) (hN : 1 ≤ N) :
    Nat.clog 2 (N + 1) ≤ Nat.clog 2 N + 1 := by
  apply Nat.clog_le_of_le_pow
  calc
    N + 1 ≤ 2 * N := by omega
    _ ≤ 2 * 2 ^ Nat.clog 2 N :=
      Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by decide) N)
    _ = 2 ^ (Nat.clog 2 N + 1) := by rw [pow_succ]; ac_rfl

theorem scalar_clog_pow_succ_le (q i : ℕ) (hq : 2 ≤ q) :
    Nat.clog 2 (q ^ i + 1) ≤ i * Nat.clog 2 q + 1 := by
  have hp : q ^ i ≤ 2 ^ (i * Nat.clog 2 q) := by
    calc
      q ^ i ≤ (2 ^ Nat.clog 2 q) ^ i :=
        Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) q) i
      _ = 2 ^ (i * Nat.clog 2 q) := by rw [← pow_mul, Nat.mul_comm]
  have hpos : 0 < q ^ i := pow_pos (by omega) _
  apply Nat.clog_le_of_le_pow
  calc
    q ^ i + 1 ≤ 2 * q ^ i := by omega
    _ ≤ 2 * 2 ^ (i * Nat.clog 2 q) := Nat.mul_le_mul_left 2 hp
    _ = 2 ^ (i * Nat.clog 2 q + 1) := by rw [pow_succ]; ac_rfl

theorem scalar_clog_le_twice_log (N : ℕ) (hN : 2 ≤ N) :
    (Nat.clog 2 N : ℝ) ≤ 2 * (Real.log (N : ℝ) / Real.log 2) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : 1 ≤ Real.logb 2 (N : ℝ) := by
    simpa only [Real.logb_self_eq_one (one_lt_two : (1 : ℝ) < 2)] using
      Real.logb_le_logb_of_le (one_lt_two : (1 : ℝ) < 2)
        (zero_lt_two : (0 : ℝ) < 2) hn
  have hk : (Nat.clog 2 N : ℝ) ≤ Real.logb 2 (N : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast 2 N]
    exact (Nat.ceil_lt_add_one (le_trans zero_le_one hx)).le
  change (Nat.clog 2 N : ℝ) ≤ 2 * Real.logb 2 (N : ℝ)
  linarith

theorem scalar_clog_succ_add_one_le_four_logb (N : ℕ) (hN : 2 ≤ N) :
    ((Nat.clog 2 (N + 1) + 1 : ℕ) : ℝ) ≤ 4 * Real.logb 2 (N : ℝ) := by
  have hn : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : 1 ≤ Real.logb 2 (N : ℝ) := by
    simpa only [Real.logb_self_eq_one (one_lt_two : (1 : ℝ) < 2)] using
      Real.logb_le_logb_of_le (one_lt_two : (1 : ℝ) < 2)
        (zero_lt_two : (0 : ℝ) < 2) hn
  have hk : (Nat.clog 2 N : ℝ) ≤ Real.logb 2 (N : ℝ) + 1 := by
    rw [← Real.natCeil_logb_natCast 2 N]
    exact (Nat.ceil_lt_add_one (le_trans zero_le_one hx)).le
  have hs : (Nat.clog 2 (N + 1) : ℝ) ≤ (Nat.clog 2 N : ℝ) + 1 := by
    exact_mod_cast scalar_clog_succ_le N (by omega)
  push_cast
  linarith

theorem scalar_log_cost_to_real (A N : ℕ) (hN : 2 ≤ N) :
    ((A * N * (Nat.clog 2 (N + 1) + 1) : ℕ) : ℝ) ≤
      (4 * (A : ℝ) / Real.log 2) * (N : ℝ) * Real.log (N : ℝ) := by
  calc
    ((A * N * (Nat.clog 2 (N + 1) + 1) : ℕ) : ℝ)
        = (A : ℝ) * (N : ℝ) * ((Nat.clog 2 (N + 1) + 1 : ℕ) : ℝ) := by
          simp only [Nat.cast_mul]
    _ ≤ (A : ℝ) * (N : ℝ) * (4 * Real.logb 2 (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (scalar_clog_succ_add_one_le_four_logb N hN)
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = (4 * (A : ℝ) / Real.log 2) * (N : ℝ) * Real.log (N : ℝ) := by
      simp only [Real.logb, div_eq_mul_inv]
      ac_rfl

theorem scalar_log_cost50_to_real (N : ℕ) (hN : 2 ≤ N) :
    ((50 * N * (Nat.clog 2 (N + 1) + 1) : ℕ) : ℝ) ≤
      (200 / Real.log 2) * (N : ℝ) * Real.log (N : ℝ) := by
  have h := scalar_log_cost_to_real 50 N hN
  norm_num at h
  simpa using h


end Prove2Me.S12.MITM

/- Inlined helper source: P089_Cost_body.lean -/
/-!
P089 charged-cost assembly. Append after the checked Generation, SortGate,
Search, and Loop helpers, plus the independently supplied scalar CostSums.
This file is a draft until a successful combined compiler log is recorded.
-/

namespace Prove2Me.S12.MITM

open MITMSynthesis

variable {α M : Type} [Monoid M] [Star M] [LinearOrder M]

theorem cost_buildS_depth_of_mem (vs : List (α × M)) (r : ℕ)
    (W : M) (c : List α) (hmem : (W, c) ∈ (buildS vs r).val) : c.length = r := by
  induction r generalizing W c with
  | zero =>
    have hp : (W, c) = (1, []) := by
      simpa only [gen_buildS_val_zero, List.mem_singleton] using hmem
    have hc : c = [] := congrArg Prod.snd hp
    simp [hc]
  | succ r ih =>
    rw [gen_buildS_val_succ, gen_extend_mem_iff] at hmem
    obtain ⟨p, hp, q, hq, heq⟩ := hmem
    have hc : q.1 :: p.2 = c := congrArg Prod.snd heq
    rw [← hc, List.length_cons, ih p.1 p.2 hp]

theorem cost_extend_depth_le (vs : List (α × M)) (prev : List (M × List α)) (B : ℕ)
    (hprev : ∀ p ∈ prev, p.2.length ≤ B) :
    ∀ p ∈ (extendC vs prev).val, p.2.length ≤ B + 1 := by
  rintro ⟨W, c⟩ hc
  obtain ⟨p, hp, q, hq, heq⟩ := (gen_extend_mem_iff vs prev W c).mp hc
  have hlabel : q.1 :: p.2 = c := congrArg Prod.snd heq
  dsimp
  rw [← hlabel, List.length_cons]
  exact Nat.add_le_add_right (hprev p hp) 1

theorem cost_query_payload_le (U : M) (arr : Array (M × List α))
    (xs : List (M × List α)) (B : ℕ) (hxs : ∀ p ∈ xs, p.2.length ≤ B)
    (c : List α) (b : M × List α)
    (hsearch : (searchAllC Prod.fst arr (queriesC U xs).val).val = some (c, b)) :
    c.length ≤ B := by
  have hq := (searchAll_sound Prod.fst arr (queriesC U xs).val c b hsearch).1
  obtain ⟨V, hV, _⟩ := (gen_queries_mem_iff U b.1 xs c).mp hq
  exact hxs (V, c) hV

/-- Charge both search passes and the largest possible output copy. A run
which returns early has a smaller cost. No sortedness or unitary assumption is
needed for this raw execution bound. -/
theorem cost_iter_upper (vs : List (α × M)) (U : M) (l i : ℕ)
    (prev : List (M × List α)) (B : ℕ) (hprev : ∀ p ∈ prev, p.2.length ≤ B) :
    let cur := (extendC vs prev).val
    let sorted := (sortC Prod.fst cur).val
    let arr := sorted.toArray
    (iterC vs U l i prev).cost ≤
      1 + (extendC vs prev).cost + (sortC Prod.fst cur).cost + (sorted.length + 1) +
        (queriesC U prev).cost + (searchAllC Prod.fst arr (queriesC U prev).val).cost +
        (queriesC U cur).cost + (searchAllC Prod.fst arr (queriesC U cur).val).cost +
        (B + 2) := by
  let cur := (extendC vs prev).val
  let sorted := (sortC Prod.fst cur).val
  let arr := sorted.toArray
  have hcur : ∀ p ∈ cur, p.2.length ≤ B + 1 := cost_extend_depth_le vs prev B hprev
  dsimp only
  cases h1 : (searchAllC Prod.fst arr (queriesC U prev).val).val with
  | some hit =>
    rcases hit with ⟨c, W, d⟩
    dsimp only [arr, sorted, cur] at h1
    have hc := cost_query_payload_le U arr prev B hprev c (W, d) h1
    simp only [iterC, gen_bind_cost, gen_bind_val, gen_pure_cost, tick, ticks, h1]
    omega
  | none =>
    dsimp only [arr, sorted, cur] at h1
    by_cases hi : 2 * i ≤ l
    · cases h2 : (searchAllC Prod.fst arr (queriesC U cur).val).val with
      | some hit =>
        rcases hit with ⟨c, W, d⟩
        dsimp only [arr, sorted, cur] at h2
        have hc := cost_query_payload_le U arr cur (B + 1) hcur c (W, d) h2
        simp only [iterC, gen_bind_cost, gen_bind_val, gen_pure_cost, tick, ticks,
          h1, if_pos hi, h2]
        omega
      | none =>
        dsimp only [arr, sorted, cur] at h2
        simp only [iterC, gen_bind_cost, gen_bind_val, gen_pure_cost, tick, ticks,
          h1, if_pos hi, h2]
        omega
    · simp only [iterC, gen_bind_cost, gen_bind_val, gen_pure_cost, tick, ticks,
        h1, if_neg hi]
      omega

/-- A coarse bound on the actual charged iteration, uniform in the target,
comparison order, and success/failure branches. -/
theorem cost_iter_generated (vs : List (α × M)) (U : M) (l r : ℕ)
    (hm : 2 ≤ vs.length) :
    (iterC vs U l (r + 1) (buildS vs r).val).cost ≤
      20 * vs.length ^ (r + 1) * (Nat.clog 2 (vs.length ^ (r + 1) + 1) + 1) := by
  let m := vs.length
  let p := m ^ r
  let n := m ^ (r + 1)
  let t := Nat.clog 2 (n + 1)
  let prev := (buildS vs r).val
  let cur := (extendC vs prev).val
  let sorted := (sortC Prod.fst cur).val
  let arr := sorted.toArray
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hdepth : r + 2 ≤ n := scalar_index_le_pow m r hm
  have hn : 1 ≤ n := by omega
  have hpn : p * m = n := (pow_succ m r).symm
  have hp : p ≤ n := by
    calc
      p ≤ p * m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left p hm1
      _ = n := hpn
  have hprevlen : prev.length = p := gen_buildS_length vs r
  have hcurval : cur = (buildS vs (r + 1)).val := (gen_buildS_val_succ vs r).symm
  have hcurlen : cur.length = n := by rw [hcurval, gen_buildS_length]
  have hslen : sorted.length = n := by
    change (sortC Prod.fst cur).val.length = n
    rw [sort_length, hcurlen]
  have hasize : arr.size = n := by
    change sorted.toArray.size = n
    simpa only [List.size_toArray] using hslen
  have hthree : p * (3 * m) = 3 * n := by
    calc
      p * (3 * m) = 3 * (p * m) := by ac_rfl
      _ = 3 * n := by rw [hpn]
  have hext : (extendC vs prev).cost ≤ 4 * n := by
    rw [gen_extend_cost, hprevlen, Nat.mul_add, Nat.mul_one]
    change p * (3 * m) + p ≤ 4 * n
    rw [hthree]
    omega
  have hsort : (sortC Prod.fst cur).cost ≤ n * (3 * t + 1) := by
    have hs := sort_cost_le_clog Prod.fst cur (by rw [hcurlen]; omega)
    rw [hcurlen] at hs
    refine hs.trans (Nat.mul_le_mul_left n ?_)
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 3 (Nat.clog_mono_right 2 (Nat.le_succ n))) 1
  have hqprev : (queriesC U prev).cost ≤ 3 * n := by
    rw [gen_queries_cost, hprevlen]
    exact Nat.mul_le_mul_left 3 hp
  have hqcur : (queriesC U cur).cost = 3 * n := by rw [gen_queries_cost, hcurlen]
  have hs1 : (searchAllC Prod.fst arr (queriesC U prev).val).cost ≤ n * (t + 2) := by
    have hs := searchAll_cost_le Prod.fst arr (queriesC U prev).val
    rw [gen_queries_length, hprevlen, hasize] at hs
    exact hs.trans (Nat.mul_le_mul_right (t + 2) hp)
  have hs2 : (searchAllC Prod.fst arr (queriesC U cur).val).cost ≤ n * (t + 2) := by
    have hs := searchAll_cost_le Prod.fst arr (queriesC U cur).val
    simpa only [gen_queries_length, hcurlen, hasize] using hs
  have hraw := cost_iter_upper vs U l (r + 1) prev r
    (fun z hz => (cost_buildS_depth_of_mem vs r z.1 z.2 hz).le)
  change (iterC vs U l (r + 1) prev).cost ≤
    1 + (extendC vs prev).cost + (sortC Prod.fst cur).cost + (sorted.length + 1) +
      (queriesC U prev).cost + (searchAllC Prod.fst arr (queriesC U prev).val).cost +
      (queriesC U cur).cost + (searchAllC Prod.fst arr (queriesC U cur).val).cost +
      (r + 2) at hraw
  rw [hslen] at hraw
  have harith := scalar_iter_cost n t hn
  change (iterC vs U l (r + 1) prev).cost ≤ 20 * n * (t + 1)
  omega

/-- Generic loop accounting. `K r` bounds the iteration that starts with the
depth-r generated list; the additional one is the loop's own tick. -/
theorem cost_loop_of_stage_bounds (vs : List (α × M)) (U : M) (l : ℕ)
    (K : ℕ → ℕ)
    (hstage : ∀ r, (iterC vs U l (r + 1) (buildS vs r).val).cost ≤ K r)
    (k r : ℕ) :
    (loopC vs U l k (r + 1) (buildS vs r).val).cost ≤
      1 + ∑ j ∈ Finset.range k, (K (r + j) + 1) := by
  induction k generalizing r with
  | zero => simp [loopC, tick]
  | succ k ih =>
    have hsum : (∑ j ∈ Finset.range (k + 1), (K (r + j) + 1)) =
        K r + 1 + ∑ j ∈ Finset.range k, (K (r + 1 + j) + 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have he : r + (j + 1) = r + 1 + j := by omega
      rw [he]
    have hiter := hstage r
    rw [loopC]
    simp only [gen_bind_cost, gen_bind_val, tick]
    cases hr : (iterC vs U l (r + 1) (buildS vs r).val).val with
    | inl c =>
      simp only [hr, gen_pure_cost]
      rw [hsum]
      omega
    | inr cur =>
      have hcur : cur = (buildS vs (r + 1)).val :=
        (iter_inr_eq vs U l (r + 1) (buildS vs r).val cur hr).trans
          (gen_buildS_val_succ vs r).symm
      simp only [hr, hcur]
      have hrec := ih (r + 1)
      rw [hsum]
      omega

theorem cost_mitm_le_loop (vs : List (α × M)) (U : M) (l : ℕ) :
    (mitmFactor vs U l).cost ≤
      1 + (loopC vs U l ((l + 1) / 2) 1 (buildS vs 0).val).cost := by
  by_cases h : compare U 1 = Ordering.eq
  · simp [mitmFactor, cmpC, h]
  · simp [mitmFactor, cmpC, h, gen_buildS_val_zero]

theorem cost_mitm_nat (vs : List (α × M)) (U : M) (l : ℕ)
    (hm : 2 ≤ vs.length) :
    (mitmFactor vs U l).cost ≤
      50 * vs.length ^ ((l + 1) / 2) *
        (Nat.clog 2 (vs.length ^ ((l + 1) / 2) + 1) + 1) := by
  let k := (l + 1) / 2
  have hloop : (loopC vs U l k 1 (buildS vs 0).val).cost ≤
      1 + ∑ j ∈ Finset.range k,
        (20 * vs.length ^ (j + 1) * (Nat.clog 2 (vs.length ^ (j + 1) + 1) + 1) + 1) := by
    simpa only [Nat.zero_add] using
      cost_loop_of_stage_bounds vs U l
        (fun r => 20 * vs.length ^ (r + 1) * (Nat.clog 2 (vs.length ^ (r + 1) + 1) + 1))
        (fun r => cost_iter_generated vs U l r hm) k 0
  have hmitm := cost_mitm_le_loop vs U l
  change (mitmFactor vs U l).cost ≤
    1 + (loopC vs U l k 1 (buildS vs 0).val).cost at hmitm
  have hscalar := scalar_total_cost_le vs.length k hm
  change (mitmFactor vs U l).cost ≤
    50 * vs.length ^ k * (Nat.clog 2 (vs.length ^ k + 1) + 1)
  omega

/-- Uniform real RAM-cost bound for the exact corrected implementation. -/
theorem cost_mitm_real (vs : List (α × M)) (U : M) (l : ℕ)
    (hm : 2 ≤ vs.length) (hl : 1 ≤ l) :
    ((mitmFactor vs U l).cost : ℝ) ≤
      (200 / Real.log 2) * (vs.length : ℝ) ^ ((l + 1) / 2) *
        Real.log ((vs.length : ℝ) ^ ((l + 1) / 2)) := by
  let k := (l + 1) / 2
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hN : 2 ≤ vs.length ^ k := by
    calc
      2 ≤ vs.length := hm
      _ = vs.length ^ 1 := (pow_one _).symm
      _ ≤ vs.length ^ k := Nat.pow_le_pow_right (by omega) hk
  have hcast : ((mitmFactor vs U l).cost : ℝ) ≤
      ((50 * vs.length ^ k * (Nat.clog 2 (vs.length ^ k + 1) + 1) : ℕ) : ℝ) := by
    exact_mod_cast cost_mitm_nat vs U l hm
  have hreal := scalar_log_cost50_to_real (vs.length ^ k) hN
  have hresult := hcast.trans hreal
  simpa only [Nat.cast_pow] using hresult

end Prove2Me.S12.MITM


/- Inlined helper source: P089_PlacementUnitary.lean -/


namespace Prove2Me.S12.MITM

open MITMSynthesis
open scoped Matrix Kronecker

attribute [local instance] Classical.propDecidable

/-- Reindexing both matrix coordinates preserves the two unitary identities. -/
theorem reindex_mem_unitary {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup J ℂ := by
  let F := Matrix.reindexRingEquiv ℂ e
  apply Matrix.mem_unitaryGroup_iff.mpr
  change F A * star (F A) = 1
  have hs : F (star A) = star (F A) := rfl
  rw [← hs, ← map_mul, hA.2, map_one]

/-- Values of the qubits outside a placement. -/
abbrev ComplementValues {n : ℕ} (p : Placement n) : Type :=
  {j : Fin n // j ∉ Set.range p.qubits} → Fin 2

/-- Split a computational basis string into selected and unselected coordinates. -/
def placementSplit {n : ℕ} (p : Placement n) :
    Q n ≃ Q p.gate.arity × ComplementValues p :=
  (Equiv.piEquivPiSubtypeProd (fun j : Fin n => j ∈ Set.range p.qubits)
    (fun _ => Fin 2)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective p.qubits p.qubits.injective).symm
        (Equiv.refl (Fin 2)))
      (Equiv.refl (ComplementValues p)))

theorem placementSplit_fst {n : ℕ} (p : Placement n) (x : Q n) :
    (placementSplit p x).1 = x ∘ p.qubits := by
  rfl

theorem placementSplit_snd {n : ℕ} (p : Placement n) (x : Q n) :
    (placementSplit p x).2 = fun j : {j : Fin n // j ∉ Set.range p.qubits} => x j := by
  rfl

/-- The exact placed-gate definition is a tensor with identity after reindexing. -/
theorem placement_eq_reindex_kronecker {n : ℕ} (p : Placement n) :
    p.unitary = Matrix.reindex (placementSplit p).symm (placementSplit p).symm
      ((p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ) ⊗ₖ
        (1 : Matrix (ComplementValues p) (ComplementValues p) ℂ)) := by
  classical
  ext x y
  change (if (∀ j, j ∉ Set.range p.qubits → x j = y j) then
      (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ)
        (x ∘ p.qubits) (y ∘ p.qubits) else 0) =
    (p.gate.mat : Matrix (Q p.gate.arity) (Q p.gate.arity) ℂ)
      (x ∘ p.qubits) (y ∘ p.qubits) *
      (if (fun j : {j : Fin n // j ∉ Set.range p.qubits} => x j) =
          (fun j : {j : Fin n // j ∉ Set.range p.qubits} => y j) then 1 else 0)
  by_cases h : ∀ j, j ∉ Set.range p.qubits → x j = y j
  · have he : (fun j : {j : Fin n // j ∉ Set.range p.qubits} => x j) =
        (fun j : {j : Fin n // j ∉ Set.range p.qubits} => y j) :=
      funext (fun j => h j j.property)
    rw [if_pos h, if_pos he, mul_one]
  · have he : (fun j : {j : Fin n // j ∉ Set.range p.qubits} => x j) ≠
        (fun j : {j : Fin n // j ∉ Set.range p.qubits} => y j) := by
      intro he
      apply h
      intro j hj
      exact congrFun he ⟨j, hj⟩
    rw [if_neg h, if_neg he, mul_zero]

theorem placement_mem_unitary {n : ℕ} (p : Placement n) :
    p.unitary ∈ Matrix.unitaryGroup (Q n) ℂ := by
  classical
  rw [placement_eq_reindex_kronecker]
  apply reindex_mem_unitary
  exact Matrix.kronecker_mem_unitary p.gate.mat.property (one_mem _)

/-- Every layer matrix is unitary, regardless of the instruction-set hypothesis. -/
theorem layer_mem_unitary {n : ℕ} (L : List (Placement n)) :
    layerUnitary L ∈ Matrix.unitaryGroup (Q n) ℂ := by
  classical
  unfold layerUnitary
  apply Submonoid.list_prod_mem
  intro A hA
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA
  exact placement_mem_unitary p

theorem depthOne_mem_unitary {n : ℕ} {G : Set Gate}
    {A : Matrix (Q n) (Q n) ℂ} (hA : A ∈ depthOneSet n G) :
    A ∈ Matrix.unitaryGroup (Q n) ℂ := by
  obtain ⟨L, hL, rfl⟩ := hA
  exact layer_mem_unitary L

end Prove2Me.S12.MITM


/- Inlined helper source: P089_Enumeration_body.lean -/
namespace Prove2Me.S12.MITM

open MITMSynthesis

variable {n : ℕ} {G : Set Gate}
variable {vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ)}

theorem enum_values_iff (hvs : IsLayerEnumeration G vs)
    (A : Matrix (Q n) (Q n) ℂ) :
    (∃ L, (L, A) ∈ vs) ↔ A ∈ depthOneSet n G := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨L, (hvs.1 (L, A) hL).1, (hvs.1 (L, A) hL).2⟩
  · intro hA
    obtain ⟨⟨L, B⟩, hp, heq⟩ := hvs.2.2 A hA
    dsimp only at heq
    subst B
    exact ⟨L, hp⟩

theorem enum_values_set (hvs : IsLayerEnumeration G vs) :
    (↑((vs.map Prod.snd).toFinset) : Set (Matrix (Q n) (Q n) ℂ)) =
      depthOneSet n G := by
  classical
  ext A
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨L, B⟩, hp, heq⟩
    dsimp only at heq
    subst B
    exact (enum_values_iff hvs A).mp ⟨L, hp⟩
  · intro hA
    obtain ⟨L, hp⟩ := (enum_values_iff hvs A).mpr hA
    exact ⟨(L, A), hp, rfl⟩

theorem enum_length_eq_ncard (hvs : IsLayerEnumeration G vs) :
    vs.length = (depthOneSet n G).ncard := by
  classical
  rw [← enum_values_set hvs, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hvs.2.1, List.length_map]

theorem enum_generated_iff_S (hvs : IsLayerEnumeration G vs)
    (i : ℕ) (A : Matrix (Q n) (Q n) ℂ) :
    (∃ c, (A, c) ∈ (buildS vs i).val) ↔ A ∈ S (depthOneSet n G) i := by
  rw [gen_buildS_value_iff]
  constructor
  · rintro ⟨values, hlen, hvalues, hprod⟩
    exact ⟨values, hlen, fun v hv => (enum_values_iff hvs v).mp (hvalues v hv), hprod⟩
  · rintro ⟨values, hlen, hvalues, hprod⟩
    exact ⟨values, hlen, fun v hv => (enum_values_iff hvs v).mpr (hvalues v hv), hprod⟩

theorem enum_generated_good (hvs : IsLayerEnumeration G vs)
    (i : ℕ) (A : Matrix (Q n) (Q n) ℂ) (c : List (List (Placement n)))
    (hmem : (A, c) ∈ (buildS vs i).val) :
    c.length = i ∧ (∀ L ∈ c, IsLayer G L) ∧ (c.map layerUnitary).prod = A := by
  have hf : ∀ p ∈ vs, layerUnitary p.1 = p.2 := fun p hp => (hvs.1 p hp).2
  obtain ⟨hlen, hlabels, hprod⟩ := (gen_buildS_mem_iff vs layerUnitary hf i A c).mp hmem
  exact ⟨hlen, fun L hL => (hvs.1 (L, layerUnitary L) (hlabels L hL)).1, hprod⟩

theorem enum_generated_unitary (hvs : IsLayerEnumeration G vs)
    (i : ℕ) (A : Matrix (Q n) (Q n) ℂ) (c : List (List (Placement n)))
    (hmem : (A, c) ∈ (buildS vs i).val) :
    A ∈ Matrix.unitaryGroup (Q n) ℂ := by
  apply gen_buildS_mem_submonoid (Matrix.unitaryGroup (Q n) ℂ) vs ?_ i A c hmem
  intro p hp
  rw [← (hvs.1 p hp).2]
  exact layer_mem_unitary p.1

end Prove2Me.S12.MITM


/- Inlined helper source: P089_Root_body.lean -/
/-!
Exact P089 root assembly. Append after the checked canonical generation,
sorting/search, loop, scalar/cost, and quantum/enumeration adapters.

The proposition below copies the published root type verbatim, changing only
the declaration name to the required global `solution`. The witness C is chosen
before every input. The formal statement has no separate positivity condition
on C. The two decision/synthesis clauses remain unconditional in l and |V|;
only the cost clause uses |V| >= 2 and l >= 1.

The instruction-set closure and target-unitarity assumptions are preserved in
the exact type. The generic proof is stronger and does not need them: all
generated factors are unitary by the physical adapter, while the target may be
arbitrary. No additional finiteness or nonemptiness hypothesis is introduced.
-/

open MITMSynthesis
open Prove2Me.S12.MITM


theorem solution :
    ∃ C : ℝ, ∀ (n : ℕ) (G : Set Gate) (vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ))
      (ord : LinearOrder (Matrix (Q n) (Q n) ℂ)) (U : Matrix (Q n) (Q n) ℂ) (l : ℕ),
      IsInstructionSet G → IsLayerEnumeration G vs → U ∈ Matrix.unitaryGroup (Q n) ℂ →
      ((mitmFactor (ord := ord) vs U l).val.isSome ↔ ∃ m ≤ l, U ∈ S (depthOneSet n G) m) ∧
      (∀ c, (mitmFactor (ord := ord) vs U l).val = some c →
        (∀ L ∈ c, IsLayer G L) ∧ (c.map layerUnitary).prod = U ∧
          IsMinDepth (depthOneSet n G) U c.length) ∧
      (2 ≤ (depthOneSet n G).ncard → 1 ≤ l →
        ((mitmFactor (ord := ord) vs U l).cost : ℝ) ≤
          C * ((depthOneSet n G).ncard : ℝ) ^ ((l + 1) / 2) *
            Real.log (((depthOneSet n G).ncard : ℝ) ^ ((l + 1) / 2))) := by
  classical
  refine ⟨200 / Real.log 2, ?_⟩
  intro n G vs ord U l _hG hvs _hU
  letI : LinearOrder (Matrix (Q n) (Q n) ℂ) := ord
  have hf : ∀ p ∈ vs, layerUnitary p.1 = p.2 :=
    fun p hp => (hvs.1 p hp).2
  have hunit : ∀ (i : ℕ) (V : Matrix (Q n) (Q n) ℂ)
      (c : List (List (Placement n))),
      (V, c) ∈ (buildS vs i).val → star V * V = 1 ∧ V * star V = 1 := by
    intro i V c hmem
    exact enum_generated_unitary hvs i V c hmem
  have hcorrect := mitm_value_correct vs layerUnitary hf hunit U l
  have hcard := enum_length_eq_ncard hvs
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hrun
      obtain ⟨m, hml, hgen⟩ := hcorrect.1.mp hrun
      exact ⟨m, hml, (enum_generated_iff_S hvs m U).mp hgen⟩
    · rintro ⟨m, hml, hS⟩
      exact hcorrect.1.mpr ⟨m, hml, (enum_generated_iff_S hvs m U).mpr hS⟩
  · intro c hc
    obtain ⟨_hlen, hmem, hminimal⟩ := hcorrect.2 c hc
    obtain ⟨_hdepth, hlayers, hproduct⟩ :=
      enum_generated_good hvs c.length U c hmem
    refine ⟨hlayers, hproduct, ?_⟩
    constructor
    · exact (enum_generated_iff_S hvs c.length U).mp ⟨c, hmem⟩
    · intro m hm
      exact hminimal m ((enum_generated_iff_S hvs m U).mpr hm)
  · intro hV hl
    have hm : 2 ≤ vs.length := by simpa only [hcard] using hV
    simpa only [hcard] using cost_mitm_real vs U l hm hl


#print axioms solution
