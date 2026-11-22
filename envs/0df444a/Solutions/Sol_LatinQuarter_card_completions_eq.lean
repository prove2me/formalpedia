-- Prove2me | solution 1 for LatinQuarter.card_completions_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:18.911786+00:00
-- url     : https://prove2.me/submissions/39d810a3-fe0b-4ee3-9431-2e6d637985b9

module
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Theorems.Thm_LatinQuarter_exists_rowChoices_of_completion
public import Theorems.Thm_LatinQuarter_chosenSquare_agrees
public import Theorems.Thm_LatinQuarter_chosenSquare_injective
public import Theorems.Thm_LatinQuarter_mem_completions
attribute [local simp] LatinQuarter.mem_completions



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
open Classical
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n)) (L : Square n)
    (hL : IsLatin L) :
    (completions P L).card =
      (Finset.univ.filter
        (fun σ : RowChoices P => IsLatin (chosenSquare P L σ))).card := by
  symm
  apply Finset.card_bij (fun σ _ => chosenSquare P L σ)
  · intro σ hσ
    exact mem_completions.mpr ⟨(Finset.mem_filter.mp hσ).2, chosenSquare_agrees P L σ⟩
  · intro σ _ τ _ h
    exact chosenSquare_injective P L hL h
  · intro M hM
    obtain ⟨hMl, hMa⟩ := mem_completions.mp hM
    obtain ⟨σ, hσ⟩ := exists_rowChoices_of_completion P L hL M hMl hMa
    refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, ?_⟩, hσ⟩
    rw [hσ]
    exact hMl
end LatinQuarter
