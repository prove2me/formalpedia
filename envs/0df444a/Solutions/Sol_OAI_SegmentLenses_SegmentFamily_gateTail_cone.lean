-- Prove2me | solution 1 for OAI.SegmentLenses.SegmentFamily.gateTail_cone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:41:15.665614+00:00
-- url     : https://prove2.me/submissions/a4315d0d-e89e-4d91-bb4e-4f12f58cfcd2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/GateRecovery.lean:L159-L173
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.SegmentFamily.gateTail_cone. The node keeps its source
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

theorem gateTail_cone (F : SegmentFamily V) {H : Finset V} {g v : V}
    (hg : Gate H g) (hv : v ∈ F.gateTail H g) : g ≤ v := by
  classical
  unfold gateTail at hv
  split_ifs at hv with h
  · let S := Classical.choose h
    have hgm : g ∈ S.val := Classical.choose_spec h
    have hvS := (Finset.mem_sdiff.mp hv).1
    rw [F.repr S] at hgm hvS
    rcases TreeOrder.lower_chain (Finset.mem_Icc.mp hgm).2
      (Finset.mem_Icc.mp hvS).2 with hle | hle
    · exact hle
    · by_contra hn
      exact (Finset.mem_sdiff.mp hv).2 (hg.2 v (lt_of_le_not_ge hle hn))
  · exact False.elim (Finset.notMem_empty _ hv)

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

theorem solution (F : SegmentFamily V) {H : Finset V} {g v : V}
    (hg : Gate H g) (hv : v ∈ F.gateTail H g) : g ≤ v := by
  first
    | exact OAI.SegmentLenses.SegmentFamily.gateTail_cone F hg hv
    | exact OAI.SegmentLenses.SegmentFamily.gateTail_cone
    | (apply OAI.SegmentLenses.SegmentFamily.gateTail_cone <;> assumption)
    | (intros; apply OAI.SegmentLenses.SegmentFamily.gateTail_cone <;> assumption)
