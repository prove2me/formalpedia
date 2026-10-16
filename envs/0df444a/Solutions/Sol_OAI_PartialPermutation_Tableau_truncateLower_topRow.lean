-- Prove2me | solution 1 for OAI.PartialPermutation.Tableau.truncateLower_topRow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:19:36.467119+00:00
-- url     : https://prove2.me/submissions/c6cc33d5-79e6-4d8f-913c-71ee0e0848b0

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Truncation.lean:L45-L58
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.Tableau.truncateLower_topRow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation

-- ---- from OAI.RepresentationTheory.PartialPermutation.Truncation ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma truncateLower_topRow (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) :
    (truncateLower μ T b).rowLen 0 = μ.rowLen 0 := by
  have hm : ∀ j, (0,j) ∈ truncateLower μ T b ↔ (0,j) ∈ μ := by
    intro j
    rw [← YoungDiagram.mem_cells, mem_truncateLower]
    exact ⟨fun h => h.choose, fun h => ⟨h,fun hn => (hn rfl).elim⟩⟩
  apply le_antisymm
  · by_contra h
    have hh := (hm (μ.rowLen 0)).mp ((truncateLower μ T b).mem_iff_lt_rowLen.mpr (by omega))
    exact (lt_irrefl _) (μ.mem_iff_lt_rowLen.mp hh)
  · by_contra h
    have hh := (hm ((truncateLower μ T b).rowLen 0)).mpr (μ.mem_iff_lt_rowLen.mpr (by omega))
    exact (lt_irrefl _) ((truncateLower μ T b).mem_iff_lt_rowLen.mp hh)

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset


theorem solution : type_of% @_root_.OAI.PartialPermutation.Tableau.truncateLower_topRow := @_root_.OAI.PartialPermutation.Tableau.truncateLower_topRow
