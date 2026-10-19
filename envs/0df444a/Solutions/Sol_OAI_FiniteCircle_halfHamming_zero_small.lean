-- Prove2me | solution 1 for OAI.FiniteCircle.halfHamming_zero_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:45:57.445987+00:00
-- url     : https://prove2.me/submissions/4a91a96e-06b3-4979-8d94-b4ef3449b719

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L312-L357
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.halfHamming_zero_small. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem zmod_val_sub_cases {M : ℕ} [NeZero M] (b v : ZMod M) :
    (b-v).val = if v.val ≤ b.val then b.val-v.val else M+b.val-v.val := by
  split_ifs with h
  · exact ZMod.val_sub h
  · have hlt : b.val < v.val := by omega
    have hv : v ≠ 0 := by intro he; simp [he] at h
    rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val, ite_eq_right hv]
    have hb := b.val_lt
    have hv' := v.val_lt
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

 theorem halfBit_interval {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v b : ZMod M) :
    halfBit v b = if v.val ≤ M/2 then
      decide (v.val ≤ b.val ∧ b.val < v.val+M/2)
    else decide (b.val < v.val-M/2 ∨ v.val ≤ b.val) := by
  unfold halfBit
  rw [zmod_val_sub_cases]
  split_ifs with h h' <;> apply Bool.eq_iff_iff.mpr <;> simp only [decide_eq_true_eq] <;>
    have hv := v.val_lt <;> have hb := b.val_lt <;> omega

 theorem halfHamming_zero_small {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v : ZMod M) (hv : v.val ≤ M/2) : halfHamming 0 v = 2*v.val := by
  classical
  let D := Finset.univ.filter (fun b : ZMod M => halfBit 0 b ≠ halfBit v b)
  have hmem (b : ZMod M) : b ∈ D ↔ b.val < v.val ∨ (M/2 ≤ b.val ∧ b.val < M/2+v.val) := by
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [halfBit_interval he, halfBit_interval he, ite_eq_left hv]
    simp only [ZMod.val_zero, Nat.zero_le, ite_true, zero_add, true_and]
    have hb := b.val_lt
    simp only [ne_eq, decide_eq_decide]
    omega
  let f : Bool × Fin v.val → ZMod M := fun a => ((if a.1 then M/2 else 0)+a.2.val : ℕ)
  have hfval (a : Bool × Fin v.val) : (f a).val = (if a.1 then M/2 else 0)+a.2.val := by
    change (((if a.1 then M/2 else 0)+a.2.val : ℕ) : ZMod M).val = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    cases a with | mk t b => cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] <;> omega
  have hcard : (Finset.univ : Finset (Bool × Fin v.val)).card = D.card := by
    apply Finset.card_bij (fun a _ => f a)
    · intro a _
      rw [hmem, hfval]
      cases a with | mk t b => cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] <;> omega
    · intro a _ b _ hab
      have hab' := congrArg ZMod.val hab
      rw [hfval, hfval] at hab'
      rcases a with ⟨ta,ia⟩
      rcases b with ⟨tb,ib⟩
      have hi := ia.isLt
      have hj := ib.isLt
      cases ta <;> cases tb <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at hab'
      · exact Prod.ext rfl (Fin.ext hab')
      · omega
      · omega
      · exact Prod.ext rfl (Fin.ext (Nat.add_left_cancel hab'))
    · intro b hb
      rw [hmem] at hb
      rcases hb with hb | hb
      · refine ⟨(false,⟨b.val,hb⟩), Finset.mem_univ _, ?_⟩
        apply ZMod.val_injective
        rw [hfval]
        simp
      · refine ⟨(true,⟨b.val-M/2, by omega⟩), Finset.mem_univ _, ?_⟩
        apply ZMod.val_injective
        rw [hfval]
        simp only [↓reduceIte]
        omega
  simpa [halfHamming, D] using hcard.symm

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.halfHamming_zero_small := @_root_.OAI.FiniteCircle.halfHamming_zero_small
