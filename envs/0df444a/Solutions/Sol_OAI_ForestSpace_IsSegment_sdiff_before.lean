-- Prove2me | solution 1 for OAI.ForestSpace.IsSegment.sdiff_before
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:34:05.461925+00:00
-- url     : https://prove2.me/submissions/dca34bf2-a054-4b33-9c05-6f2e26b4a232

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/FiniteGeometry.lean:L69-L83
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.IsSegment.sdiff_before. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry

-- ---- from OAI.Analysis.ForestSpace.FiniteGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteGeometry
variable {V : Type} [Fintype V] [PartialOrder V]

/-- Removing a terminal suffix from any segment leaves a segment. -/
 theorem IsSegment.sdiff_before {S : Finset V} (hS : IsSegment S) {a b g : V}
    (hSa : S = before a g) : IsSegment (S \ before b g) := by
  classical
  subst S
  constructor
  · intro v hv w hw
    exact hS.1 v (mem_sdiff.mp hv).1 w (mem_sdiff.mp hw).1
  · intro v hv w hw z hvz hzw
    have hz := hS.2 v (mem_sdiff.mp hv).1 w (mem_sdiff.mp hw).1 z hvz hzw
    refine mem_sdiff.mpr ⟨hz, ?_⟩
    intro hzb
    apply (mem_sdiff.mp hw).2
    exact mem_before.mpr ⟨(mem_before.mp hzb).1.trans hzw,
      (mem_before.mp (mem_sdiff.mp hw).1).2⟩

end FiniteGeometry

section CrossTermAlgebra

end CrossTermAlgebra

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.IsSegment.sdiff_before := @_root_.OAI.ForestSpace.IsSegment.sdiff_before
