-- Prove2me | solution 2 for OAI.Saxl.colTruncate_rowLen
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:27:45.244479+00:00
-- url     : https://prove2.me/submissions/d2c31176-d338-44b0-b2aa-fef196110230

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/DominatedSupport.lean:L19-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.colTruncate_rowLen. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseSign
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedQuotient
import Definitions.Def_OAI_RepresentationTheory_Saxl_DominatedSupport

-- ---- from OAI.RepresentationTheory.Saxl.DominatedSupport ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
open scoped MonoidAlgebra

end Saxl

namespace Saxl

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.colTruncate_rowLen := @_root_.OAI.Saxl.colTruncate_rowLen
