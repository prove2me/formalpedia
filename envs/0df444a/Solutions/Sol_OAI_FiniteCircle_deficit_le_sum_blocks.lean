-- Prove2me | solution 1 for OAI.FiniteCircle.deficit_le_sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:45:40.922014+00:00
-- url     : https://prove2.me/submissions/0c0388fd-6035-497d-bb1a-2a724e159322

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Windows.lean:L155-L175
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.deficit_le_sum_blocks. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows

-- ---- from OAI.Combinatorics.FiniteCircle.Windows ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem lcs_append_ge {α : Type*} (x y u v : List α) :
    lcs x y + lcs u v ≤ lcs (x ++ u) (y ++ v) := by
  obtain ⟨z, hzx, hzy, hz⟩ := lcs_exists x y
  obtain ⟨t, htu, htv, ht⟩ := lcs_exists u v
  simpa [List.length_append, hz, ht] using le_lcs (hzx.append htu) (hzy.append htv)

theorem deficit_append_le {α : Type*} (x y u v : List α) :
    deficit (x ++ u) (y ++ v) ≤ deficit x y + deficit u v := by
  have h := lcs_append_ge x y u v
  have hx := lcs_le_length_left x y
  have hu := lcs_le_length_left u v
  simp only [deficit, List.length_append]
  omega

theorem deficit_le_sum_blocks {α : Type*} {x y : List α} {b m : ℕ}
    (hx : x.length = b*m) (hy : y.length = b*m) :
    deficit x y ≤ ∑ j : Fin b, deficit (segment x (j*m) m) (segment y (j*m) m) := by
  induction b generalizing x y with
  | zero =>
    have hx0 : x = [] := List.length_eq_zero_iff.mp (by simpa using hx)
    have hy0 : y = [] := List.length_eq_zero_iff.mp (by simpa using hy)
    simp [hx0, hy0, deficit]
  | succ b ih =>
    have hxt : (x.drop m).length = b*m := by simp only [List.length_drop]; rw [hx, Nat.succ_mul]; omega
    have hyt : (y.drop m).length = b*m := by simp only [List.length_drop]; rw [hy, Nat.succ_mul]; omega
    have hd := deficit_append_le (x.take m) (y.take m) (x.drop m) (y.drop m)
    simp only [List.take_append_drop] at hd
    refine hd.trans ?_
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.zero_mul, segment, List.drop_zero]
    apply Nat.add_le_add_left
    convert ih hxt hyt using 1
    apply Finset.sum_congr rfl
    intro j _
    simp [segment, List.drop_drop, Fin.val_succ, Nat.add_mul, Nat.add_comm]

open scoped BigOperators List

open scoped BigOperators

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.deficit_le_sum_blocks := @_root_.OAI.FiniteCircle.deficit_le_sum_blocks
