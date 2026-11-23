-- Prove2me | solution 1 for KernelRank.separableRank_comp_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:24:48.696936+00:00
-- url     : https://prove2.me/submissions/e412c12b-349d-49d8-8d38-c364f5d34e32

import Mathlib
import Definitions.Def_KernelRankLean_Defs
import Theorems.Thm_KernelRank_IsSumOfProducts_comp

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} (K : (∀ i, X i) → 𝕜) {g : ∀ i, Y i → X i}
    (hg : ∀ i, Function.Surjective (g i)) :
    separableRank (fun y => K fun i => g i (y i)) = separableRank K := by
  refine le_antisymm (le_iInf₂ fun N hN => iInf₂_le N (hN.comp g)) ?_
  refine le_iInf₂ fun N hN => ?_
  have hinv := hN.comp fun i => Function.surjInv (hg i)
  have heq : (fun x : ∀ i, X i => K fun i => g i (Function.surjInv (hg i) (x i))) = K := by
    funext x
    congr 1
    funext i
    exact Function.surjInv_eq (hg i) (x i)
  rw [heq] at hinv
  exact iInf₂_le N hinv
end KernelRank
