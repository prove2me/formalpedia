-- Prove2me | solution 1 for LatinQuarter.columnSymbol_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:40.951776+00:00
-- url     : https://prove2.me/submissions/8362ca65-a2ec-4e97-8534-06051ed9f3ff

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
theorem _root_.solution {n : ℕ} {M : Square n} (hM : IsLatin M) :
    Function.Bijective (columnSymbol M) := by
  apply Function.Injective.bijective_of_finite
  intro p q hpq
  have hc : p.2 = q.2 := congrArg Prod.fst hpq
  have hs : M p.1 p.2 = M q.1 q.2 := congrArg Prod.snd hpq
  apply Prod.ext
  · apply (hM.2 p.2).injective
    simpa only [columnSymbol, ← hc] using hs
  · exact hc
end LatinQuarter
