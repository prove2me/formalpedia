-- Prove2me | solution 1 for OAI.SegmentLenses.split_interval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:24:29.969528+00:00
-- url     : https://prove2.me/submissions/7e53b26d-6e39-4188-89be-687d8e5ee772

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/TreeGeometry.lean:L121-L137
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.split_interval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry

-- ---- from OAI.Analysis.SegmentLenses.TreeGeometry ----
namespace OAI

/-!
# Ancestry, segment splitting, and opposite crossings
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section TreeGeometry
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem split_interval {a c b : V} (hac : a ≤ c) (hcb : c ≤ b) :
    Finset.Ico a c ∪ Finset.Icc c b = Finset.Icc a b := by
  have _ := segmentSystemV
  have _ := intervalSegmentsV
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro (⟨hav, hvc⟩ | ⟨hcv, hvb⟩)
    · exact ⟨hav, le_trans hvc.le hcb⟩
    · exact ⟨le_trans hac hcv, hvb⟩
  · rintro ⟨hav, hvb⟩
    rcases TreeOrder.lower_chain hvb hcb with hvc | hcv
    · rcases lt_or_eq_of_le hvc with hlt | rfl
      · exact Or.inl ⟨hav, hlt⟩
      · exact Or.inr ⟨le_rfl, hcb⟩
    · exact Or.inr ⟨hcv, hvb⟩

namespace SegmentFamily

end SegmentFamily

end TreeGeometry

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [segmentSystemV : SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem solution {a c b : V} (hac : a ≤ c) (hcb : c ≤ b) :
    Finset.Ico a c ∪ Finset.Icc c b = Finset.Icc a b := by
  first
    | exact OAI.SegmentLenses.split_interval hac hcb
    | exact OAI.SegmentLenses.split_interval
    | (apply OAI.SegmentLenses.split_interval <;> assumption)
    | (intros; apply OAI.SegmentLenses.split_interval <;> assumption)
