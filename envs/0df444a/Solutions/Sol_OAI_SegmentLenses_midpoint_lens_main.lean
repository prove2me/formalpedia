-- Prove2me | solution 1 for OAI.SegmentLenses.midpoint_lens_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:52:55.621108+00:00
-- url     : https://prove2.me/submissions/8744bbb0-2ace-4eef-bfd8-a92ff091dc4b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Main.lean:L7-L16
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.SegmentLenses.midpoint_lens_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_SegmentLenses_midpoint_lens_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_Completed
import Theorems.Thm_OAI_SegmentLenses_completed_main_tail

-- ---- from OAI.Analysis.SegmentLenses.Completed ----
namespace OAI

/-!
# Completed midpoint bounds and coordinate density
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section FiniteAncestry
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrderBot V]

end FiniteAncestry

section LocalizingTests
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

end LocalizingTests

section CompletedMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

end CompletedMain

theorem forest_main_tail (H : Finset ForestVertex) (hH : Ancestral ForestAncestor H)
    (x y : X) (hx : x = head H x) (R : ℝ) (hR : 0 ≤ R)
    (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) :=
  by
    classical
    exact completed_main_tail hH x y hx.symm R hR hp hm

theorem infinite_main_tail (H : Finset InfiniteVertex) (hH : Ancestral List.IsPrefix H)
    (x y : BInfinite) (hx : x.val = head H x.val) (R : ℝ) (hR : 0 ≤ R)
    (hp : ‖x + y‖ ≤ R) (hm : ‖x - y‖ ≤ R) :
    ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2) :=
  by
    classical
    exact completed_main_tail hH x.val y.val hx.symm R hR hp hm

section CoordinateNorms
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end CoordinateNorms

section CoordinateDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end CoordinateDensity

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.Main ----
namespace OAI

namespace SegmentLenses

theorem midpoint_lens_main :
    (∀ (H : Finset ForestVertex) (_ : Ancestral ForestAncestor H)
      (x y : X) (_ : x = head H x) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∧
    (∀ (H : Finset InfiniteVertex) (_ : Ancestral List.IsPrefix H)
      (x y : BInfinite) (_ : x.val = head H x.val) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) :=
  ⟨forest_main_tail, infinite_main_tail⟩

end SegmentLenses

end OAI

-- ---- mission target ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset

theorem solution :
    (∀ (H : Finset ForestVertex) (_ : Ancestral ForestAncestor H)
      (x y : X) (_ : x = head H x) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) ∧
    (∀ (H : Finset InfiniteVertex) (_ : Ancestral List.IsPrefix H)
      (x y : BInfinite) (_ : x.val = head H x.val) (R : ℝ) (_ : 0 ≤ R)
      (_ : ‖x + y‖ ≤ R) (_ : ‖x - y‖ ≤ R),
      ‖tail H y.val‖ ≤ 2 * Real.sqrt (R ^ 2 - ‖x‖ ^ 2)) := by
  first
    | exact OAI.SegmentLenses.midpoint_lens_main
    | (apply OAI.SegmentLenses.midpoint_lens_main <;> assumption)
    | (intros; apply OAI.SegmentLenses.midpoint_lens_main <;> assumption)
