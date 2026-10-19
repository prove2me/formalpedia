-- Prove2me | solution 1 for OAI.FiniteCircle.halfHamming_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:47:23.216099+00:00
-- url     : https://prove2.me/submissions/d540c7c4-04b1-4400-9e0e-c6f1d65ed934

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L359-L376
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.halfHamming_eq. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_halfHamming_translate
import Theorems.Thm_OAI_FiniteCircle_halfHamming_zero_small

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem halfHamming_symm {M : ℕ} [NeZero M] (v w : ZMod M) :
    halfHamming v w = halfHamming w v := by
  unfold halfHamming
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]

 theorem halfHamming_zero_neg {M : ℕ} [NeZero M] (v : ZMod M) :
    halfHamming 0 (-v) = halfHamming 0 v := by
  have h := halfHamming_translate (0 : ZMod M) (-v) v
  simp only [zero_add, neg_add_cancel] at h
  exact h.symm.trans (halfHamming_symm _ _)

 theorem halfHamming_eq {M : ℕ} [NeZero M] (he : M = 2*(M/2))
    (v w : ZMod M) : halfHamming v w = 2*(w-v).valMinAbs.natAbs := by
  have ht : halfHamming v w = halfHamming 0 (w-v) := by
    have hh := halfHamming_translate v w (-v)
    simpa only [add_neg_cancel, ← sub_eq_add_neg] using hh.symm
  rw [ht]
  by_cases h : (w-v).val ≤ M/2
  · rw [halfHamming_zero_small he _ h, ZMod.valMinAbs_def_pos, ite_eq_left h, Int.natAbs_natCast]
  · have hh : (-(w-v)).val ≤ M/2 := by
      rw [ZMod.neg_val, ite_eq_right]
      · have hv := (w-v).val_lt
        omega
      · intro hz
        simp [hz] at h
    rw [← halfHamming_zero_neg (w-v), halfHamming_zero_small he _ hh]
    have ha : (-(w-v)).valMinAbs.natAbs = (-(w-v)).val := by
      rw [ZMod.valMinAbs_def_pos, ite_eq_left hh, Int.natAbs_natCast]
    rw [← ha, ZMod.natAbs_valMinAbs_neg]

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.halfHamming_eq := @_root_.OAI.FiniteCircle.halfHamming_eq
