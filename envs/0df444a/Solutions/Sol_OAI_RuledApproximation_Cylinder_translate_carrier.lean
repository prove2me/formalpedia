-- Prove2me | solution 1 for OAI.RuledApproximation.Cylinder.translate_carrier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:55:35.474344+00:00
-- url     : https://prove2.me/submissions/0279484d-ca13-42bd-b17e-447f26426979

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Isometries.lean:L77-L91
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.Cylinder.translate_carrier. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries

-- ---- from OAI.Geometry.RuledCovering.Isometries ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma Cylinder.translate_carrier (C : Cylinder) (q : Space) :
    (C.translate q).carrier = (fun x => q + x) '' C.carrier := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, t, rfl⟩
    refine ⟨(b : Space) + (t - inner ℝ C.axis q) • C.axis,
      ⟨b, hb, _, rfl⟩, ?_⟩
    change q + ((b : Space) + (t - inner ℝ C.axis q) • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + t • C.axis
    module
  · rintro ⟨_, ⟨b, hb, t, rfl⟩, rfl⟩
    refine ⟨C.transversePart q + b, ⟨b, hb, rfl⟩, t + inner ℝ C.axis q, ?_⟩
    change q + ((b : Space) + t • C.axis) =
      (q - (inner ℝ C.axis q) • C.axis + b) + (t + inner ℝ C.axis q) • C.axis
    module

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.Cylinder.translate_carrier := @_root_.OAI.RuledApproximation.Cylinder.translate_carrier
