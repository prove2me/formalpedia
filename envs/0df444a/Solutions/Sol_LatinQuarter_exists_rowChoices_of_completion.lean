-- Prove2me | solution 1 for LatinQuarter.exists_rowChoices_of_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:23.705181+00:00
-- url     : https://prove2.me/submissions/a7ece7bd-d18a-41c7-986b-28f9f5f9be43

module
public import Definitions.Def_LeanPool_LatinQuarter_LowerBound
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_free



set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
open MvPolynomial
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (P : Finset (Cell n))
    (L : Square n) (hL : IsLatin L) (M : Square n) (hM : IsLatin M)
    (ha : Agrees P L M) : ∃ σ : RowChoices P, chosenSquare P L σ = M := by
  -- In row `r`, the free cell `c` of `M` holds the symbol that `L` has in
  -- column `(L r)⁻¹ (M r c)`, and that column is also free.
  have hfree : ∀ (r : Fin n) (c : FreeColumn P r),
      (r, (Equiv.ofBijective (L r) (hL.1 r)).symm (M r c)) ∉ P := by
    intro r c hmem
    have hLd : L r ((Equiv.ofBijective (L r) (hL.1 r)).symm (M r c)) = M r c :=
      Equiv.ofBijective_apply_symm_apply (L r) (hL.1 r) (M r c)
    have hMd := ha _ hmem
    have hdc : (Equiv.ofBijective (L r) (hL.1 r)).symm (M r c) = c.val :=
      (hM.1 r).injective (hMd.trans hLd)
    rw [hdc] at hmem
    exact c.property hmem
  let f : (r : Fin n) → FreeColumn P r → FreeColumn P r := fun r c =>
    ⟨(Equiv.ofBijective (L r) (hL.1 r)).symm (M r c), hfree r c⟩
  have hf : ∀ r, Function.Injective (f r) := by
    intro r c c' h
    have h1 := congrArg Subtype.val h
    have h2 := (Equiv.ofBijective (L r) (hL.1 r)).symm.injective h1
    exact Subtype.ext ((hM.1 r).injective h2)
  let σ : RowChoices P := fun r => Equiv.ofBijective (f r) (hf r).bijective_of_finite
  refine ⟨σ, ?_⟩
  funext r c
  by_cases hc : (r, c) ∈ P
  · rw [chosenSquare_clue P L σ r c hc]
    exact (ha (r, c) hc).symm
  · calc chosenSquare P L σ r c = L r (σ r ⟨c, hc⟩) := chosenSquare_free P L σ r ⟨c, hc⟩
      _ = M r c := Equiv.ofBijective_apply_symm_apply (L r) (hL.1 r) (M r c)
end LatinQuarter
