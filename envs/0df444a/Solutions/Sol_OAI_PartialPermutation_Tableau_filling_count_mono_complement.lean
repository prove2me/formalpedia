-- Prove2me | solution 1 for OAI.PartialPermutation.Tableau.filling_count_mono_complement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:16:29.932605+00:00
-- url     : https://prove2.me/submissions/83fbb2db-94a8-420a-89ef-681b5f7108e4

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/FillingExtensions.lean:L75-L88
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.Tableau.filling_count_mono_complement. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.PartialPermutation.FillingExtensions ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Extension
variable {α β : Type*} [Fintype α] [PartialOrder α] [Fintype β] [PartialOrder β]

lemma filling_count_mono_complement (P : α → Prop) [DecidablePred P]
    (hP : IsLowerSet {a | P a}) :
    Fintype.card (StandardFilling {a // ¬P a}) ≤ Fintype.card (StandardFilling α) := by
  let T := chosenFilling {a // P a}
  apply Fintype.card_le_of_injective (fun U => extendFilling P hP T U)
  intro U V he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  have h := congrArg (fun S : StandardFilling α => (S.1 a.1).val) he
  change (concatEnumeration P T U a.1).val = (concatEnumeration P T V a.1).val at h
  simp only [concatEnumeration_neg P _ _ _ a.2] at h
  exact Nat.add_left_cancel h

end Extension

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset


theorem solution : type_of% @_root_.OAI.PartialPermutation.Tableau.filling_count_mono_complement := @_root_.OAI.PartialPermutation.Tableau.filling_count_mono_complement
