-- Prove2me | solution 1 for OAI.FiniteCircle.get_encode_block
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:16:21.208184+00:00
-- url     : https://prove2.me/submissions/bfc4f013-1b08-47c3-84ab-f936e4e7b19f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BlockMatching.lean:L11-L31
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.get_encode_block. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching

-- ---- from OAI.Combinatorics.FiniteCircle.BlockMatching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem get_encode_block {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (x : List α) (i : Fin x.length) (r : Fin w) :
    (encode c x).get ⟨i.val * w + r.val, by
      rw [length_encode]
      nlinarith [i.isLt, r.isLt]⟩ = c (x.get i) r := by
  induction x with
  | nil => exact Fin.elim0 i
  | cons a x ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, encode_cons, List.get_eq_getElem,
        List.getElem_cons_zero]
      rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact r.isLt), List.getElem_ofFn]
    · have hit : (j.val+1)*w+r.val < (List.ofFn (c a) ++ encode c x).length := by
        simp only [List.length_append, List.length_ofFn, length_encode]
        nlinarith [j.isLt, r.isLt]
      change (List.ofFn (c a) ++ encode c x)[(j.val+1)*w+r.val] = c (x.get j) r
      rw [List.getElem_append_right (by simp only [List.length_ofFn]; nlinarith)]
      convert ih j using 1
      simp only [List.length_ofFn, List.get_eq_getElem]
      congr 1
      simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.get_encode_block := @_root_.OAI.FiniteCircle.get_encode_block
