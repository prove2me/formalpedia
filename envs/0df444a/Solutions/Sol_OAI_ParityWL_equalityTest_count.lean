-- Prove2me | solution 1 for OAI.ParityWL.equalityTest_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:32:15.009279+00:00
-- url     : https://prove2.me/submissions/fc8bf8a9-4eb8-47c1-9e53-e272dacaea03

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean:L34-L59
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.equalityTest_count. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra

-- ---- from OAI.Combinatorics.ParityLifts.TestAlgebra ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section AtomicTests

open scoped Classical

variable {k t : ℕ}

lemma equalityTest_count (hkt : k ≤ t) (i j : Fin k) {V : Type} [Fintype V]
    (G : SimpleGraph V) (x : Fin k → V) :
    (equalityTest hkt i j).count G x = if x i = x j then 1 else 0 := by
  by_cases h : x i = x j
  · rw [ite_eq_left h]
    let f : (equalityTest hkt i j).Maps G x :=
      ⟨⟨Quot.lift x (by rintro a b ⟨rfl, rfl⟩; exact h), fun _ _ h => h.elim⟩,
        fun _ => rfl⟩
    have : Unique ((equalityTest hkt i j).Maps G x) :=
      { default := f
        uniq := by
          intro g
          apply Subtype.ext
          apply Subtype.ext
          funext q
          induction q using Quot.inductionOn with
          | h a => exact g.2 a }
    simp only [RootedTest.count, Fintype.card_unique, Nat.cast_one]
  · rw [ite_eq_right h]
    have : IsEmpty ((equalityTest hkt i j).Maps G x) := ⟨by
      intro g
      apply h
      rw [← g.2 i, ← g.2 j]
      apply congrArg g.1.1
      exact Quot.sound ⟨rfl, rfl⟩⟩
    simp only [RootedTest.count, Fintype.card_eq_zero, Nat.cast_zero]

end AtomicTests

section TestAlgebra

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)

end TestAlgebra

section TestOperations

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

end TestOperations

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.equalityTest_count := @_root_.OAI.ParityWL.equalityTest_count
