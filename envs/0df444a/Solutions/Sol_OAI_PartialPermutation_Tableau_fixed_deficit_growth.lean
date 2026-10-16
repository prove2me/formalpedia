-- Prove2me | solution 1 for OAI.PartialPermutation.Tableau.fixed_deficit_growth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:24:48.2517+00:00
-- url     : https://prove2.me/submissions/3cea34fb-664d-4bf5-8287-c587165831e3

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TailBounds.lean:L112-L125
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.Tableau.fixed_deficit_growth. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Theorems.Thm_OAI_PartialPermutation_Tableau_binomial_lower_bound

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

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.TailBounds ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

lemma standardCount_transpose (μ : YoungDiagram) : standardCount μ.transpose = standardCount μ :=
  (Fintype.card_congr (fillingCongr (transposeCellsEquiv μ))).symm

lemma card_transpose (μ : YoungDiagram) : μ.transpose.cells.card = μ.cells.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (transposeCellsEquiv μ).toEquiv).symm

lemma longest_binomial_lower_bound (μ : YoungDiagram) (b : ℕ)
    (hb : b ≤ min (maxLine μ) (deficit μ)) :
    (maxLine μ).choose b ≤ standardCount μ := by
  by_cases h : μ.colLen 0 ≤ μ.rowLen 0
  · have he : maxLine μ=μ.rowLen 0 := max_eq_left h
    rw [he]
    exact binomial_lower_bound μ b (by simpa only [deficit,he] using hb)
  · have hb' : b ≤ min (μ.transpose.rowLen 0)
        (μ.transpose.cells.card - μ.transpose.rowLen 0) := by
      simpa only [deficit,maxLine,max_eq_right (le_of_not_ge h),
        card_transpose,YoungDiagram.rowLen_transpose] using hb
    simpa only [YoungDiagram.rowLen_transpose,standardCount_transpose,
      maxLine,max_eq_right (le_of_not_ge h)] using binomial_lower_bound μ.transpose b hb'

lemma linear_le_choose (a k : ℕ) (hk : 0 < k) (hka : k ≤ a) : a-k+1 ≤ a.choose k := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hka
  simp only [Nat.add_sub_cancel_left]
  induction r with
  | zero => simp
  | succ r ih =>
    have hk' : k-1 ≤ k+r := by omega
    have hpos := Nat.choose_pos hk'
    have he : (k+(r+1)).choose k = (k+r).choose (k-1)+(k+r).choose k := by
      have h := Nat.choose_succ_succ (k+r) (k-1)
      simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1≤k by omega), Nat.add_assoc] using h
    rw [he]
    omega

lemma fixed_deficit_growth (μ : YoungDiagram) (hk : 0 < deficit μ)
    (hlarge : 2*deficit μ ≤ μ.cells.card) :
    μ.cells.card-2*deficit μ+1 ≤ standardCount μ := by
  have hLle : maxLine μ ≤ μ.cells.card := by
    apply max_le
    · exact topRow_le_card μ
    · have h:=topRow_le_card μ.transpose
      simpa only [YoungDiagram.rowLen_transpose,card_transpose] using h
  have hkL : deficit μ ≤ maxLine μ := by unfold deficit at *; omega
  have he : μ.cells.card-2*deficit μ=maxLine μ-deficit μ := by
    unfold deficit at *; omega
  rw [he]
  exact (linear_le_choose _ _ hk hkL).trans
    (longest_binomial_lower_bound μ (deficit μ) (le_min hkL le_rfl))

end
end Tableau
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset


theorem solution : type_of% @_root_.OAI.PartialPermutation.Tableau.fixed_deficit_growth := @_root_.OAI.PartialPermutation.Tableau.fixed_deficit_growth
