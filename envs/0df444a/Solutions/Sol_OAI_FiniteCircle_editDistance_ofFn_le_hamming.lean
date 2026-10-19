-- Prove2me | solution 1 for OAI.FiniteCircle.editDistance_ofFn_le_hamming
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:40:47.689855+00:00
-- url     : https://prove2.me/submissions/811b95d5-053b-43be-b1c6-a454a8979f12

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Translations.lean:L36-L60
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.editDistance_ofFn_le_hamming. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

theorem append_left (h : EditStep x y) (u : List α) : EditStep (u ++ x) (u ++ y) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc] using EditStep.insert (u ++ p) q a
  | delete p q a => simpa only [List.append_assoc] using EditStep.delete (u ++ p) q a
  | substitute p q a b =>
    simpa only [List.append_assoc] using EditStep.substitute (u ++ p) q a b

theorem append_right (h : EditStep x y) (v : List α) : EditStep (x ++ v) (y ++ v) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.insert p (q ++ v) a
  | delete p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.delete p (q ++ v) a
  | substitute p q a b =>
    simpa only [List.append_assoc, List.cons_append] using EditStep.substitute p (q ++ v) a b

end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

theorem append_left (h : EditScript n x y) (u : List α) : EditScript n (u ++ x) (u ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left u) ih

theorem append_right (h : EditScript n x y) (v : List α) : EditScript n (x ++ v) (y ++ v) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right v) ih

end EditScript

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Translations ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem editDistance_append_le {α : Type*} (x y x' y' : List α) :
    editDistance (x++y) (x'++y') ≤ editDistance x x' + editDistance y y' := by
  apply editDistance_le_of_script
  exact ((editDistance_spec x x').append_right y).trans ((editDistance_spec y y').append_left x')

 theorem editDistance_ofFn_le_hamming {α : Type*} [DecidableEq α] {N : ℕ} (f g : Fin N → α) :
    editDistance (List.ofFn f) (List.ofFn g) ≤
      (Finset.univ.filter fun i => f i ≠ g i).card := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have he : ∀ a b : α, editDistance [a] [b] ≤ if a=b then 0 else 1 := by
      intro a b
      split_ifs with h
      · subst b
        simp
      · apply editDistance_le_of_script
        exact EditScript.one (.substitute [] [] a b)
    rw [List.ofFn_succ, List.ofFn_succ]
    have ht := editDistance_append_le [f 0] (List.ofFn (fun i => f i.succ))
      [g 0] (List.ofFn (fun i => g i.succ))
    have hi := ih (fun i => f i.succ) (fun i => g i.succ)
    have hcard : (Finset.univ.filter fun i : Fin (N+1) => f i ≠ g i).card =
        (if f 0 = g 0 then 0 else 1) +
        (Finset.univ.filter fun i : Fin N => f i.succ ≠ g i.succ).card := by
      simp only [Finset.card_filter, Fin.sum_univ_succ]
      split_ifs <;> simp_all
    rw [hcard]
    exact ht.trans (Nat.add_le_add (he _ _) hi)

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.editDistance_ofFn_le_hamming := @_root_.OAI.FiniteCircle.editDistance_ofFn_le_hamming
