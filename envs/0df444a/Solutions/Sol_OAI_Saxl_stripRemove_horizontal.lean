-- Prove2me | solution 1 for OAI.Saxl.stripRemove_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:03:05.762753+00:00
-- url     : https://prove2.me/submissions/3a4a3d69-1938-42f9-9b75-f6cfea5e9ea2

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HorizontalRemoval.lean:L78-L94
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.stripRemove_horizontal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval

-- ---- from OAI.RepresentationTheory.Saxl.HorizontalRemoval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Tallest-column bottom deletion, expressed by interlacing rows. -/
lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma stripRemove_horizontal (μ : YoungDiagram) (t : ℕ) : HorizontalStrip (stripRemove μ t) μ := by
  refine ⟨stripRemove_le μ t, ?_⟩
  intro x hx hxn y hy hyn hcol
  have hhx := YoungDiagram.mem_iff_lt_rowLen.mp hx
  have hhy := YoungDiagram.mem_iff_lt_rowLen.mp hy
  have hnx : stripRow μ t x.1 ≤ x.2 := le_of_not_gt (fun h => hxn (mem_stripRemove.mpr h))
  have hny : stripRow μ t y.1 ≤ y.2 := le_of_not_gt (fun h => hyn (mem_stripRemove.mpr h))
  have hr : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hr | hr | hr
    · have hh := μ.rowLen_anti (x.1+1) y.1 (by omega)
      have hb := (stripRow_bounds μ t x.1).1
      omega
    · exact hr
    · have hh := μ.rowLen_anti (y.1+1) x.1 (by omega)
      have hb := (stripRow_bounds μ t y.1).1
      omega
  exact Prod.ext hr hcol

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.stripRemove_horizontal := @_root_.OAI.Saxl.stripRemove_horizontal
