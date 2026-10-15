-- Prove2me | solution 1 for OAI.SegmentLenses.SegmentFamily.gateTail_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:39:39.856976+00:00
-- url     : https://prove2.me/submissions/75305d98-6fef-49d7-9a78-7f06edc5c8a9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/GateRecovery.lean:L141-L157
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.SegmentFamily.gateTail_segment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
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

-- ---- from OAI.Analysis.SegmentLenses.GateRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Gate coefficients, cone recovery, and energy budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section ProjectionAlgebra
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

namespace SegmentFamily

end SegmentFamily

namespace Representation

end Representation
end ProjectionAlgebra

section GateTails
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace SegmentFamily

theorem gateTail_segment (F : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (g : V) :
    F.gateTail H g = ∅ ∨ SegmentSystem.isSegment (F.gateTail H g) := by
  classical
  unfold gateTail
  split_ifs with h
  · let S := Classical.choose h
    apply subinterval_isSegment (F.segment S.val S.property) Finset.sdiff_subset
    intro a ha b hb v hav hvb
    have hS : v ∈ S.val := by
      rw [F.repr S] at ha hb ⊢
      have ha' := (Finset.mem_sdiff.mp ha).1
      have hb' := (Finset.mem_sdiff.mp hb).1
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha').1.trans hav,
        hvb.trans (Finset.mem_Icc.mp hb').2⟩
    exact Finset.mem_sdiff.mpr ⟨hS, fun hv => (Finset.mem_sdiff.mp ha).2 (hH hv hav)⟩
  · exact Or.inl rfl

end SegmentFamily
end GateTails

section GateRecovery
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

namespace SegmentFamily

end SegmentFamily
end GateRecovery

section ScaledLaws
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace Representation

end Representation

end ScaledLaws

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses OAI.SegmentLenses.SegmentFamily
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem solution (F : SegmentFamily V) {H : Finset V}
    (hH : Ancestral (· ≤ ·) H) (g : V) :
    F.gateTail H g = ∅ ∨ SegmentSystem.isSegment (F.gateTail H g) := by
  first
    | exact OAI.SegmentLenses.SegmentFamily.gateTail_segment F hH g
    | exact OAI.SegmentLenses.SegmentFamily.gateTail_segment
    | (apply OAI.SegmentLenses.SegmentFamily.gateTail_segment <;> assumption)
    | (intros; apply OAI.SegmentLenses.SegmentFamily.gateTail_segment <;> assumption)
