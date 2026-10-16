-- Prove2me | solution 1 for OAI.PartialPermutation.Tableau.binomial_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:20:59.138877+00:00
-- url     : https://prove2.me/submissions/600eb1d3-5404-4da7-a93f-6d4415bb7ef9

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/Truncation.lean:L105-L118
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.Tableau.binomial_lower_bound. The node keeps its source
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
import Theorems.Thm_OAI_PartialPermutation_Tableau_row_interleaving_lower_bound
import Theorems.Thm_OAI_PartialPermutation_Tableau_truncateLower_topRow

-- ---- from OAI.RepresentationTheory.PartialPermutation.FillingExtensions ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Extension
variable {α β : Type*} [Fintype α] [PartialOrder α] [Fintype β] [PartialOrder β]

lemma filling_count_mono_lowerSet (P : α → Prop) [DecidablePred P]
    (hP : IsLowerSet {a | P a}) :
    Fintype.card (StandardFilling {a // P a}) ≤ Fintype.card (StandardFilling α) := by
  let U := chosenFilling {a // ¬P a}
  apply Fintype.card_le_of_injective (fun T => extendFilling P hP T U)
  intro T S he
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply Fin.ext
  have h := congrArg (fun T : StandardFilling α => (T.1 a.1).val) he
  change (concatEnumeration P T U a.1).val = (concatEnumeration P S U a.1).val at h
  simpa only [concatEnumeration_pos P _ _ _ a.2] using h

end Extension

lemma standardCount_mono {μ ν : YoungDiagram} (h : μ ≤ ν) :
    standardCount μ ≤ standardCount ν := by
  classical
  have hh : IsLowerSet {x : ν.cells | x.1 ∈ μ.cells} := by
    intro x y hxy hy
    exact μ.isLowerSet hxy hy
  have hcard := Fintype.card_congr (fillingCongr (subdiagramCellsEquiv h))
  unfold standardCount
  rw [hcard]
  exact filling_count_mono_lowerSet _ hh

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.RowBounds ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma topRow_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.cells.card := by
  have h := Fintype.card_le_of_injective (topRowEquiv μ).symm
    (topRowEquiv μ).symm.injective
  have h' := Fintype.card_subtype_le (fun x : μ.cells => x.1.1=0)
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.trans h'

lemma secondRow_le_lower (μ : YoungDiagram) : μ.rowLen 1 ≤ μ.cells.card-μ.rowLen 0 := by
  let f : Fin (μ.rowLen 1) → {x : μ.cells // x.1.1 ≠ 0} := fun i =>
    ⟨⟨(1,i), μ.mem_iff_lt_rowLen.mpr i.2⟩,Nat.one_ne_zero⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : {x : μ.cells // x.1.1 ≠ 0} => x.1.1.2) hij
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, lower_card] using h

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.Truncation ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma truncateLower_card (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ)
    (hb : b ≤ μ.cells.card - μ.rowLen 0) :
    (truncateLower μ T b).cells.card = μ.rowLen 0 + b := by
  have h := Fintype.card_congr (truncatedLowerEquiv μ T b hb)
  rw [Fintype.card_fin, lower_card, truncateLower_topRow] at h
  have hle := topRow_le_card (truncateLower μ T b)
  rw [truncateLower_topRow] at hle
  omega

lemma binomial_lower_bound (μ : YoungDiagram) (b : ℕ)
    (hb : b ≤ min (μ.rowLen 0) (μ.cells.card-μ.rowLen 0)) :
    (μ.rowLen 0).choose b ≤ standardCount μ := by
  let T := chosenFilling {x : μ.cells // x.1.1≠0}
  let ν := truncateLower μ T b
  have hb' := hb.trans (min_le_right _ _)
  have htop : ν.rowLen 0 = μ.rowLen 0 := truncateLower_topRow μ T b
  have hcard : ν.cells.card = μ.rowLen 0 + b := truncateLower_card μ T b hb'
  have hsecond := secondRow_le_lower ν
  rw [htop,hcard,Nat.add_sub_cancel_left] at hsecond
  have h := row_interleaving_lower_bound ν
  rw [htop,hcard,Nat.add_sub_cancel_left] at h
  exact ((Nat.choose_le_choose b (show μ.rowLen 0 ≤ μ.rowLen 0+b-ν.rowLen 1 by omega)).trans h).trans
    (standardCount_mono (truncateLower_le μ T b))

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset


theorem solution : type_of% @_root_.OAI.PartialPermutation.Tableau.binomial_lower_bound := @_root_.OAI.PartialPermutation.Tableau.binomial_lower_bound
