-- Prove2me | solution 1 for OAI.ParityWL.separate_indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:46:55.755609+00:00
-- url     : https://prove2.me/submissions/1ac8a5f3-244f-489d-96c9-f873a517afae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/ColorSpan.lean:L145-L177
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.separate_indicator_mem. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan
import Theorems.Thm_OAI_ParityWL_atomic_indicator_mem
import Theorems.Thm_OAI_ParityWL_color_indicator_mem_of_separation
import Theorems.Thm_OAI_ParityWL_testSpan_replacementSum

-- ---- from OAI.Combinatorics.ParityLifts.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

lemma count_map_as_sum {X D : Type} [Fintype X] [DecidableEq D] (c : X → D) (d : D) :
    (Multiset.count d (Finset.univ.val.map c) : ℚ) =
      ∑ x : X, if c x = d then (1 : ℚ) else 0 := by
  rw [Multiset.count_map, Finset.sum_boole]
  congr 1
  exact congrArg Multiset.card (by
    apply Multiset.filter_congr
    intro x _
    exact eq_comm)

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

end RefinementOperators

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.ColorSpan ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section ColorSpan

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma separate_indicator_sum {k r : ℕ} (i : Fin k) (d : SeparateColor k r)
    (a : TuplePair V W k) :
    replacementSum i (fun x => if pairSeparate G H k r x = d then (1 : ℚ) else 0) a =
      (Multiset.count d ((pairSeparate G H k (r + 1) a).2 i) : ℚ) := by
  cases a with
  | inl x => exact (count_map_as_sum _ _).symm
  | inr x => exact (count_map_as_sum _ _).symm

lemma pairSeparate_zero {k : ℕ} (a : TuplePair V W k) :
    pairSeparate G H k 0 a = pairAtomic G H a := by
  cases a <;> rfl

lemma pairJoint_fst {k r : ℕ} (a : TuplePair V W k) :
    (pairJoint G H k (r + 1) a).1 = pairJoint G H k r a := by
  cases a <;> rfl

lemma pairSeparate_fst {k r : ℕ} (a : TuplePair V W k) :
    (pairSeparate G H k (r + 1) a).1 = pairSeparate G H k r a := by
  cases a <;> rfl

lemma separate_indicator_mem {k t : ℕ} (hkt : k ≤ t) (r : ℕ) (d : SeparateColor k r) :
    (fun x => if pairSeparate G H k r x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by
  induction r with
  | zero =>
    convert atomic_indicator_mem G H hkt d using 1
    funext x
    split_ifs <;> simp_all [pairSeparate_zero]
    contradiction
  | succ r ih =>
    refine color_indicator_mem_of_separation (testAlgebra G H k t hkt)
      (pairSeparate G H k (r+1)) ?_ d
    intro x y hxy
    by_contra! hn
    apply hxy
    apply Prod.ext
    · rw [pairSeparate_fst, pairSeparate_fst]
      have hf := ih (pairSeparate G H k r x)
      have he := hn _ hf (by
        intro z w hzw
        have hz : pairSeparate G H k r z = pairSeparate G H k r w := by
          simpa only [pairJoint_fst, pairSeparate_fst] using congrArg Prod.fst hzw
        rw [hz])
      by_contra hne
      simp only [ite_eq_right (Ne.symm hne), ite_true, one_ne_zero] at he
    · funext i
      apply Multiset.ext.mpr
      intro e
      have hf := testSpan_replacementSum G H hkt i (ih e)
      have he := hn _ hf (by
        intro z w hzw
        rw [separate_indicator_sum, separate_indicator_sum, hzw])
      rw [separate_indicator_sum, separate_indicator_sum] at he
      exact_mod_cast he

end ColorSpan

section SpanHistograms

open scoped Classical

variable {V W X Y D : Type} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]
variable (G : SimpleGraph V) (H : SimpleGraph W) {k t : ℕ}
variable (l : X → TuplePair V W k) (r : Y → TuplePair V W k)

end SpanHistograms

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.separate_indicator_mem := @_root_.OAI.ParityWL.separate_indicator_mem
