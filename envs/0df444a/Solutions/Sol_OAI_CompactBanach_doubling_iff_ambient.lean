-- Prove2me | solution 1 for OAI.CompactBanach.doubling_iff_ambient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:26:52.125457+00:00
-- url     : https://prove2.me/submissions/920232dd-d7b9-4fd7-aa59-d31df910a9c8

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/IntrinsicCovers.lean:L16-L37
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.doubling_iff_ambient. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers

-- ---- from OAI.Geometry.DoublingHilbert.IntrinsicCovers ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

theorem doubling_iff_ambient {B : Type*} [MetricSpace B] {K : Set B} {bound : ℕ} :
    DoublingAtMost K bound ↔ AmbientDoubling K bound := by
  classical
  constructor
  · intro h x hx r hr
    obtain ⟨c, hc, hcov⟩ := h ⟨x, hx⟩ r hr
    refine ⟨c.image Subtype.val, ?_, (Finset.card_image_le).trans hc, ?_⟩
    · intro z hz
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
      exact w.property
    · intro y hy hxy
      obtain ⟨z, hz, hzy⟩ := hcov ⟨y, hy⟩ hxy
      exact ⟨z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, hzy⟩
  · intro h x r hr
    obtain ⟨c, hc, hcard, hcov⟩ := h x x.property r hr
    let cs : Finset K := c.attach.image fun z => ⟨z.val, hc z.val z.property⟩
    refine ⟨cs, ?_, ?_⟩
    · exact (Finset.card_image_le).trans (by simpa using hcard)
    · intro y hxy
      obtain ⟨z, hz, hzy⟩ := hcov y y.property hxy
      refine ⟨⟨z, hc z hz⟩, ?_, hzy⟩
      exact Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩

                                                                                    
end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CompactBanach.doubling_iff_ambient := @_root_.OAI.CompactBanach.doubling_iff_ambient
