-- Prove2me | solution 1 for OAI.SegmentLenses.Representation.norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:29:54.187122+00:00
-- url     : https://prove2.me/submissions/2b37c89c-5a10-47c7-987c-8e68e919e0d5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Pairing.lean:L159-L174
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.Representation.norm_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing

-- ---- from OAI.Analysis.SegmentLenses.Pairing ----
namespace OAI

/-!
# Finite heads and the completion–dual pairing
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section Restrictions
variable {V : Type*} [decidableEqV : DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end Restrictions

section Pairing
variable {V : Type*} [SegmentSystem V]

theorem Representation.norm_le (A : Representation V) :
    ‖A.value‖ ≤ Real.sqrt A.energy := by
  apply dual_norm_le _ (Real.sqrt_nonneg _)
  intro u
  rw [A.apply_test]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun S => |A.coeff S|) (fun S => |∑ v ∈ S.val, u.coeff v|)
  simp only [sq_abs, ← A.family.seminorm_sq, Real.sqrt_sq (apply_nonneg _ _)] at h
  calc
    |∑ S, A.coeff S * ∑ v ∈ S.val, u.coeff v| ≤
        ∑ S, |A.coeff S| * |∑ v ∈ S.val, u.coeff v| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun S => A.coeff S * ∑ v ∈ S.val, u.coeff v) Finset.univ
    _ ≤ Real.sqrt A.energy * A.family.seminorm u.coeff := h
    _ ≤ Real.sqrt A.energy * ‖u‖ :=
      mul_le_mul_of_nonneg_left (le_segmentSeminorm _ _) (Real.sqrt_nonneg _)

end Pairing

section MorePairing
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end MorePairing

section DualRestrictions
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end DualRestrictions

section IndexedFamilies
variable {V ι : Type*} [DecidableEq V] [SegmentSystem V] [Fintype ι]

end IndexedFamilies

section ClipFamilies
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end ClipFamilies

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [SegmentSystem V]

theorem solution (A : Representation V) :
    ‖A.value‖ ≤ Real.sqrt A.energy := by
  first
    | exact OAI.SegmentLenses.Representation.norm_le A
    | exact OAI.SegmentLenses.Representation.norm_le
    | (apply OAI.SegmentLenses.Representation.norm_le <;> assumption)
    | (intros; apply OAI.SegmentLenses.Representation.norm_le <;> assumption)
