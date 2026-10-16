-- Prove2me | solution 1 for OAI.PartialPermutation.Tableau.row_interleaving_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:17:44.25174+00:00
-- url     : https://prove2.me/submissions/796ef1b7-d649-481b-a8f0-d2c2ec596b97

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/RowBounds.lean:L65-L89
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.Tableau.row_interleaving_lower_bound. The node keeps its source
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
import Theorems.Thm_OAI_PartialPermutation_Tableau_filling_count_mono_complement

-- ---- from OAI.RepresentationTheory.PartialPermutation.Interleavings ----
namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

section Interleave
variable {α : Type*} [Fintype α] [PartialOrder α]

lemma interleaveFilling_injective (P : α → Prop) [DecidablePred P]
    (hP : ∀ a b, a < b → (P a ↔ P b))
    (T : StandardFilling {a // P a}) (U : StandardFilling {a // ¬P a}) :
    Function.Injective (interleaveFilling P hP T U) := by
  intro s t hst
  have hval := congrArg Subtype.val hst
  have hsr : Set.range (fun a : {a // P a} => interleavingEnumeration P T U s a.1) = s.1 := by
    have heq : (fun a : {a // P a} => interleavingEnumeration P T U s a.1) =
        (s.1.orderEmbOfFin s.2) ∘ T.1 := by
      funext a
      exact interleavingEnumeration_pos P T U s a.1 a.2
    rw [heq, Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  have htr : Set.range (fun a : {a // P a} => interleavingEnumeration P T U t a.1) = t.1 := by
    have heq : (fun a : {a // P a} => interleavingEnumeration P T U t a.1) =
        (t.1.orderEmbOfFin t.2) ∘ T.1 := by
      funext a
      exact interleavingEnumeration_pos P T U t a.1 a.2
    rw [heq, Set.range_comp, Equiv.range_eq_univ, Set.image_univ, Finset.range_orderEmbOfFin]
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← hsr, ← htr]
  congr 1
  funext a
  exact Equiv.congr_fun hval a.1

lemma interleaving_binomial_lower_bound (P : α → Prop) [DecidablePred P]
    (hP : ∀ a b, a < b → (P a ↔ P b)) :
    (Fintype.card α).choose (Fintype.card {a // P a}) ≤
      Fintype.card (StandardFilling α) := by
  have h := Fintype.card_le_of_injective
    (interleaveFilling P hP (chosenFilling _) (chosenFilling _))
    (interleaveFilling_injective P hP (chosenFilling _) (chosenFilling _))
  simpa only [Fintype.card_finset_len, Fintype.card_fin] using h
end Interleave

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

lemma topPrefix_lower (μ : YoungDiagram) (c : ℕ) :
    IsLowerSet {x | topPrefix μ c x} := by
  intro x y hxy hy
  exact ⟨Nat.eq_zero_of_le_zero (hxy.1.trans_eq hy.1), hxy.2.trans_lt hy.2⟩

lemma topPrefix_card (μ : YoungDiagram) (c : ℕ) (hc : c ≤ μ.rowLen 0) :
    Fintype.card {x // topPrefix μ c x} = c := by
  simpa using Fintype.card_congr (topPrefixEquiv μ c hc)

lemma prefix_upper_card (μ : YoungDiagram) (c : ℕ) (hc : c ≤ μ.rowLen 0) :
    Fintype.card {x // ¬topPrefix μ c x} = μ.cells.card-c := by
  rw [Fintype.card_subtype_compl, topPrefix_card μ c hc, Fintype.card_coe]

lemma row_interleaving_lower_bound (μ : YoungDiagram) :
    (μ.cells.card-μ.rowLen 1).choose (μ.cells.card-μ.rowLen 0) ≤ standardCount μ := by
  let P := topPrefix μ (μ.rowLen 1)
  let Q : {x // ¬P x} → Prop := fun x => x.1.1.1 ≠ 0
  have hP := topPrefix_lower μ (μ.rowLen 1)
  have hQ : ∀ a b : {x // ¬P x}, a < b → (Q a ↔ Q b) := by
    intro a b hab
    change (a.1.1.1 ≠ 0 ↔ b.1.1.1 ≠ 0)
    have hi := hab.le.1
    have hj := hab.le.2
    constructor
    · intro ha hb
      exact ha (Nat.eq_zero_of_le_zero (hi.trans_eq hb))
    · intro hb ha
      have hcol : b.1.1.2 < μ.rowLen 1 :=
        (μ.mem_iff_lt_rowLen.mp b.1.2).trans_le (μ.rowLen_anti 1 b.1.1.1 (by omega))
      exact a.2 ⟨ha,hj.trans_lt hcol⟩
  have h := interleaving_binomial_lower_bound Q hQ
  have hc : μ.rowLen 1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 1 (by omega)
  have hcard : Fintype.card {x : {x // ¬P x} // Q x} = μ.cells.card-μ.rowLen 0 :=
    (Fintype.card_congr (lowerInUpperEquiv μ (μ.rowLen 1))).trans (lower_card μ)
  rw [hcard] at h
  have hu : Fintype.card {x // ¬P x} = μ.cells.card-μ.rowLen 1 := prefix_upper_card μ _ hc
  rw [hu] at h
  exact h.trans (filling_count_mono_complement P hP)

end
end Tableau
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.Tableau
open Finset


theorem solution : type_of% @_root_.OAI.PartialPermutation.Tableau.row_interleaving_lower_bound := @_root_.OAI.PartialPermutation.Tableau.row_interleaving_lower_bound
