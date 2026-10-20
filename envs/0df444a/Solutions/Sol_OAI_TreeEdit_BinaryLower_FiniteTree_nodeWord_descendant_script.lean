-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_script
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:46:55.714265+00:00
-- url     : https://prove2.me/submissions/f92ebc99-98c7-4444-a1b4-8e5dc383d4b3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeCosts.lean:L51-L125
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_script. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteTree_nodeWord_invariant

-- ---- from OAI.Combinatorics.BinaryEdit.CheapTranslations ----
namespace OAI

/-!
# Inexpensive translations

Elementary unrestricted edit scripts give the translation estimates in
`lem:finite-cost`.
-/

namespace TreeEdit.BinaryLower.CheapTranslations

universe u v

variable {α : Type u}

theorem unitEdit_prefix {x y : List α} (p : List α)
    (h : EditStep x y) : EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q s a =>
      simpa only [List.append_assoc] using EditStep.insert (p ++ q) s a
  | delete q s a =>
      simpa only [List.append_assoc] using EditStep.delete (p ++ q) s a
  | substitute q s a b =>
      simpa only [List.append_assoc] using EditStep.substitute (p ++ q) s a b

theorem script_prefix {x y : List α} {n : ℕ} (p : List α)
    (h : EditScript x y n) : EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil x => exact EditScript.nil _
  | cons step tail ih => exact EditScript.cons (unitEdit_prefix p step) ih

theorem unitEdit_suffix {x y : List α} (q : List α)
    (h : EditStep x y) : EditStep (x ++ q) (y ++ q) := by
  cases h with
  | insert p s a =>
      simpa only [List.append_assoc, List.cons_append] using
        EditStep.insert p (s ++ q) a
  | delete p s a =>
      simpa only [List.append_assoc, List.cons_append] using
        EditStep.delete p (s ++ q) a
  | substitute p s a b =>
      simpa only [List.append_assoc, List.cons_append] using
        EditStep.substitute p (s ++ q) a b

theorem script_suffix {x y : List α} {n : ℕ} (q : List α)
    (h : EditScript x y n) : EditScript (x ++ q) (y ++ q) n := by
  induction h with
  | nil x => exact EditScript.nil _
  | cons step tail ih => exact EditScript.cons (unitEdit_suffix q step) ih

theorem script_trans {x y z : List α} {m n : ℕ}
    (hxy : EditScript x y m) (hyz : EditScript y z n) :
    EditScript x z (m + n) := by
  induction hxy with
  | nil x => simpa using hyz
  | cons step tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EditScript.cons step (ih hyz)

/-- Scripts in corresponding concatenated blocks add their costs. This
allows a local row translation to be performed separately at every copy of
a descendant word, without altering the other blocks. -/
theorem script_flatMap {ι : Type v} (indices : List ι)
    (f g : ι → List α) (cost : ι → ℕ)
    (h : ∀ i ∈ indices, EditScript (f i) (g i) (cost i)) :
    EditScript (indices.flatMap f) (indices.flatMap g)
      ((indices.map cost).sum) := by
  induction indices with
  | nil => exact EditScript.nil []
  | cons i indices ih =>
      have hi := h i List.mem_cons_self
      have ht : ∀ j ∈ indices, EditScript (f j) (g j) (cost j) := by
        intro j hj
        exact h j (List.mem_cons_of_mem i hj)
      simpa only [List.flatMap_cons, List.map_cons, List.sum_cons] using
        script_trans (script_suffix (indices.flatMap f) hi)
          (script_prefix (g i) (ih ht))

end TreeEdit.BinaryLower.CheapTranslations

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteTreeCosts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Inexpensive scripts in the recursive row evaluator

Local row advancement and descendant-occurrence lifting establish
`lem:finite-cost` from geometric hypotheses on state translations and
invisible leaf decoders.
-/

namespace TreeEdit.BinaryLower.FiniteTree

open CheapTranslations

variable {A Γ : Type*} [AddCommMonoid A]

/-- A uniform script at one descendant lifts through its `T^q.length`
occurrences. Leaf decoders outside that descendant must be invariant under
the same state translation. Every intermediate word remains unrestricted. -/
theorem nodeWord_descendant_script {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (q p : List (Fin m)) (z : A) (C : ℕ)
    (hlocal : ∀ y, EditScript (nodeWord T leaf u h (p ++ q) y)
      (nodeWord T leaf u h (p ++ q) (y + z)) C)
    (houtside : ∀ r : List (Fin m), r.length = h + q.length →
      ¬ q.IsPrefix r → ∀ y, leaf (p ++ r) (y + z) = leaf (p ++ r) y)
    (x : A) :
    EditScript (nodeWord T leaf u (h + q.length) p x)
      (nodeWord T leaf u (h + q.length) p (x + z)) (T ^ q.length * C) := by
  classical
  induction q generalizing p x with
  | nil => simpa using hlocal x
  | cons i q ih =>
      have htarget (y : A) :
          EditScript (nodeWord T leaf u (h + q.length) (p ++ [i]) y)
            (nodeWord T leaf u (h + q.length) (p ++ [i]) (y + z))
            (T ^ q.length * C) := by
        apply ih (p := p ++ [i]) (x := y)
        · intro v
          simpa only [List.append_assoc, List.singleton_append] using hlocal v
        · intro r hr hn v
          have hlen : (i :: r).length = h + (i :: q).length := by
            simp only [List.length_cons, hr]
            omega
          have hnot : ¬ (i :: q).IsPrefix (i :: r) := by
            simpa only [List.cons_prefix_cons, true_and] using hn
          simpa only [List.append_assoc, List.singleton_append] using
            houtside (i :: r) hlen hnot v
      have hchild (a : ℕ) (j : Fin m) :
          EditScript
            (nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
            (nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
            (if j = i then T ^ q.length * C else 0) := by
        rw [add_right_comm x z]
        by_cases hji : j = i
        · subst j
          simpa only [ite_true] using htarget (x + a • u p)
        · simp only [ite_eq_right hji]
          have hinv : ∀ r : List (Fin m), r.length = h + q.length → ∀ y,
              leaf ((p ++ [j]) ++ r) (y + z) = leaf ((p ++ [j]) ++ r) y := by
            intro r hr y
            have hlen : (j :: r).length = h + (i :: q).length := by
              simp only [List.length_cons, hr]
              omega
            have hnot : ¬ (i :: q).IsPrefix (j :: r) := by
              simp only [List.cons_prefix_cons, Ne.symm hji, false_and, not_false_eq_true]
            simpa only [List.append_assoc, List.singleton_append] using
              houtside (j :: r) hlen hnot y
          rw [nodeWord_invariant T leaf u (h + q.length) (p ++ [j]) z hinv]
          exact EditScript.nil _
      have hrow (a : ℕ) :
          EditScript
            ((List.finRange m).flatMap fun j =>
              nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
            ((List.finRange m).flatMap fun j =>
              nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
            (T ^ q.length * C) := by
        have hs := script_flatMap (List.finRange m)
          (fun j => nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
          (fun j => nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
          (fun j => if j = i then T ^ q.length * C else 0)
          (fun j _ => hchild a j)
        simpa [List.finRange, List.sum_ofFn, Function.comp_def] using hs
      have hs := script_flatMap (List.range T)
        (fun a => (List.finRange m).flatMap fun j =>
          nodeWord T leaf u (h + q.length) (p ++ [j]) (x + a • u p))
        (fun a => (List.finRange m).flatMap fun j =>
          nodeWord T leaf u (h + q.length) (p ++ [j]) (x + z + a • u p))
        (fun _ => T ^ q.length * C) (fun a _ => hrow a)
      simpa [nodeWord, Nat.add_assoc, pow_succ, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hs

end TreeEdit.BinaryLower.FiniteTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteTree
open CheapTranslations


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_script := @_root_.OAI.TreeEdit.BinaryLower.FiniteTree.nodeWord_descendant_script
