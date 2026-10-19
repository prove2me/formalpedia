-- Prove2me | solution 1 for OAI.FiniteCircle.lcs_taggedRow_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:34:28.254986+00:00
-- url     : https://prove2.me/submissions/7ac7f81a-aa28-46f2-905b-4efb5b04fde3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean:L62-L75
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.lcs_taggedRow_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

end EditScript

theorem lcs_map_ge {α β : Type*} (f : α → β) (x y : List α) :
    lcs x y ≤ lcs (x.map f) (y.map f) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have h := le_lcs (hx.map f) (hy.map f)
  simpa only [List.length_map, hz] using h

theorem lcs_map_eq {α β : Type*} (f : α → β) (hf : Function.Injective f) (x y : List α) :
    lcs (x.map f) (y.map f) = lcs x y := by
  apply Nat.le_antisymm _ (lcs_map_ge f x y)
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists (x.map f) (y.map f)
  obtain ⟨u, hux, hu⟩ := List.sublist_map_iff.mp hx
  obtain ⟨v, hvy, hv⟩ := List.sublist_map_iff.mp hy
  have huv : u = v := List.map_injective_iff.mpr hf (hu.symm.trans hv)
  subst v
  have h := le_lcs hux hvy
  rw [← hz, hu, List.length_map]
  exact h

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.TaggedRows ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem filter_map_tag {J β : Type*} [DecidableEq J] (j k : J) (x : List β) :
    ((x.map (fun b => (k,b))).filter (fun z => decide (z.1 = j))) =
      if k = j then x.map (fun b => (j,b)) else [] := by
  by_cases h : k = j
  · subst k
    simp [List.filter_map, Function.comp_def]
  · simp [List.filter_map, Function.comp_def, h]

theorem filter_taggedRow {J β : Type*} [DecidableEq J] (js : List J)
    (hn : js.Nodup) (W : J → List β) (j : J) :
    ((taggedRow js W).filter (fun z => decide (z.1 = j))) =
      if j ∈ js then (W j).map (fun b => (j,b)) else [] := by
  induction js with
  | nil => simp
  | cons k js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [taggedRow_cons, List.filter_append, filter_map_tag, ih hn'.2]
    by_cases h : k = j
    · subst k
      simp [hn'.1]
    · by_cases hj : j ∈ js <;> simp [h, hj, Ne.symm h]

theorem sum_filter_tag_length {J β : Type*} [Fintype J] [DecidableEq J]
    (x : List (J × β)) :
    ∑ j : J, (x.filter (fun z => decide (z.1 = j))).length = x.length := by
  induction x with
  | nil => simp
  | cons a x ih =>
    have he (j : J) : ((a::x).filter (fun z => decide (z.1 = j))).length =
        (if a.1 = j then 1 else 0) + (x.filter (fun z => decide (z.1 = j))).length := by
      by_cases h : a.1 = j <;> simp [h, Nat.add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

theorem lcs_taggedRow_le {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W U : J → List β) :
    lcs (taggedRow js W) (taggedRow js U) ≤ ∑ j : J, lcs (W j) (U j) := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists (taggedRow js W) (taggedRow js U)
  rw [← hz, ← sum_filter_tag_length z]
  apply Finset.sum_le_sum
  intro j _
  have hx' := hx.filter (fun z => decide (z.1 = j))
  have hy' := hy.filter (fun z => decide (z.1 = j))
  rw [filter_taggedRow js hn W j, ite_eq_left (hall j)] at hx'
  rw [filter_taggedRow js hn U j, ite_eq_left (hall j)] at hy'
  have hh := le_lcs hx' hy'
  rw [lcs_map_eq (fun b : β => (j,b)) (fun _ _ h => congrArg Prod.snd h)] at hh
  exact hh

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

end WordMatching

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.lcs_taggedRow_le := @_root_.OAI.FiniteCircle.lcs_taggedRow_le
