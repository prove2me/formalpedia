-- Prove2me | solution 1 for LatinQuarter.full_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:29.044001+00:00
-- url     : https://prove2.me/submissions/9d0b348e-645f-4d66-9048-78a53c97907b

module
public import Definitions.Def_LeanPool_LatinQuarter_Rows
public import Definitions.Def_LeanPool_LatinQuarter_Tags
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Counting
public import Theorems.Thm_LatinQuarter_columnSymbol_bijective
public import Theorems.Thm_LatinQuarter_isLatin_of_columnSymbol_injective
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_coeff_allTags_product
public import Theorems.Thm_LatinQuarter_mem_completions
public import Theorems.Thm_LatinQuarter_product_eq_zero_of_repeated_square_zero
public import Theorems.Thm_LatinQuarter_squarefree_coeff_zero_of_quotient_zero
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
open Classical
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (M : Square n)
    (hr : ∀ r, Function.Bijective (M r)) :
    (∏ p : Cell n, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)).coeff
      (allTagsExponent (Cell n)) =
      if IsLatin M then 1 else 0 := by
  classical
  by_cases hM : IsLatin M
  · rw [if_pos hM]
    have hp := (Equiv.ofBijective (columnSymbol M) (columnSymbol_bijective hM)).prod_comp
      (fun p => (X p : MvPolynomial (Cell n) (ZMod 2)))
    change (∏ p, X (columnSymbol M p) : MvPolynomial (Cell n) (ZMod 2)) = ∏ p, X p at hp
    rw [hp]
    exact coeff_allTags_product
  · rw [if_neg hM]
    have hn : ¬ Function.Injective (columnSymbol M) :=
      fun hi => hM (isLatin_of_columnSymbol_injective hr hi)
    simp only [Function.Injective, not_forall] at hn
    obtain ⟨p, q, hpq⟩ := hn
    have he : columnSymbol M p = columnSymbol M q := by tauto
    have hne : p ≠ q := by tauto
    apply squarefree_coeff_zero_of_quotient_zero _ (by simp)
    simp only [map_prod]
    change (∏ p : Cell n, tag (columnSymbol M p)) = 0
    exact product_eq_zero_of_repeated_square_zero _ hne (congrArg tag he) (tag_sq _)
end LatinQuarter
