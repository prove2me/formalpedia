-- Prove2me | solution 1 for OAI.FiniteCircle.halfCircle_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:52:48.283433+00:00
-- url     : https://prove2.me/submissions/390dcd9d-e6c9-42c0-9973-a2b22f8d5828

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L406-L421
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.halfCircle_separation. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_halfHamming_eq
import Theorems.Thm_OAI_FiniteCircle_halfHamming_fin
import Theorems.Thm_OAI_FiniteCircle_hamming_le_five_deficit

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

 theorem halfBit_thresholds {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v : ZMod M) :
    ∀ i j : Fin M, halfBit v (i.val : ZMod M) ≠ halfBit v (j.val : ZMod M) →
      (i.val < v.val ∧ v.val ≤ j.val) ∨ (j.val < v.val ∧ v.val ≤ i.val) ∨
      (i.val < (v.val+M/2)%M ∧ (v.val+M/2)%M ≤ j.val) ∨
      (j.val < (v.val+M/2)%M ∧ (v.val+M/2)%M ≤ i.val) := by
  intro i j hij
  rw [halfBit_interval he, halfBit_interval he] at hij
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij
  by_cases hv : v.val < M/2
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)] at hij
    rw [Nat.mod_eq_of_lt (by omega : v.val+M/2 < M)]
    have hh : ¬ ((v.val ≤ i.val ∧ i.val < v.val+M/2) ↔
      (v.val ≤ j.val ∧ j.val < v.val+M/2)) := by simpa only [ne_eq, decide_eq_decide] using hij
    omega
  · have hmod : (v.val+M/2)%M = v.val-M/2 := by
      have hval := v.val_lt
      have hh : v.val+M/2 = (v.val-M/2)+M := by omega
      rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    by_cases hv' : v.val = M/2
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), hv'] at hij
      have hi := i.isLt; have hj := j.isLt
      have hh : ¬ ((M/2 ≤ i.val ∧ i.val < M/2+M/2) ↔
        (M/2 ≤ j.val ∧ j.val < M/2+M/2)) := by simpa only [ne_eq, decide_eq_decide] using hij
      omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hij
      have hh : ¬ ((i.val < v.val-M/2 ∨ v.val ≤ i.val) ↔
        (j.val < v.val-M/2 ∨ v.val ≤ j.val)) := by simpa only [ne_eq, decide_eq_decide] using hij
      omega

 theorem halfCircle_separation {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v θ : ZMod M) :
    (M:ℝ)*circleCost θ/4 ≤
      (deficit (List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)))
        (List.ofFn (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))) : ℝ) := by
  have hh := hamming_le_five_deficit
    (fun i : Fin M => halfBit v (i.val : ZMod M))
    (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))
    (v+θ).val (((v+θ).val+M/2)%M) (halfBit_thresholds he (v+θ))
  rw [halfHamming_fin, halfHamming_eq he, add_sub_cancel_left] at hh
  have hr : 2*(θ.valMinAbs.natAbs : ℝ) ≤ 5*
      (deficit (List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)))
        (List.ofFn (fun i : Fin M => halfBit (v+θ) (i.val : ZMod M))) : ℝ) := by exact_mod_cast hh
  have hM : (M:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [circleCost, mul_div_cancel₀ _ hM]
  nlinarith [Nat.cast_nonneg (α := ℝ) θ.valMinAbs.natAbs]

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.halfCircle_separation := @_root_.OAI.FiniteCircle.halfCircle_separation
