-- Prove2me | solution 1 for LatinQuarter.expand_row_matchings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:14.349855+00:00
-- url     : https://prove2.me/submissions/f34fba76-8fb0-4dcd-ae8d-b932ce35dcc0

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_det_eq_matching_sum
public import Theorems.Thm_LatinQuarter_mem_completions
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_one
attribute [local simp] LatinQuarter.mem_completions
attribute [local simp] LatinQuarter.tag_sq



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {n : ℕ} {R : Type*} [CommRing R] [CharP R 2]
    (P : Finset (Cell n)) (L : Square n) (Y : Matrix (Fin n) (Fin n) R) :
    clueProduct P L Y * rowMinorProduct P L Y =
      ∑ σ : RowChoices P, ∏ p : Cell n, Y p.2 (chosenSquare P L σ p.1 p.2) := by
  classical
  unfold rowMinorProduct
  simp_rw [det_eq_matching_sum]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fintype.prod_prod_type]
  unfold clueProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _
  have hp := Fintype.prod_subtype_mul_prod_subtype (fun c : Fin n => (r, c) ∈ P)
    (fun c => Y c (chosenSquare P L σ r c))
  convert hp using 1
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro c _
      rw [chosenSquare_clue P L σ r c c.property]
    · apply Finset.prod_congr rfl
      intro c _
      simp only [Matrix.submatrix_apply, chosenSquare_free]
end LatinQuarter
