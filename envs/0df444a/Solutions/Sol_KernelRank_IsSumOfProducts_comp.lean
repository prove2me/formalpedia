-- Prove2me | solution 1 for KernelRank.IsSumOfProducts.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:39.474813+00:00
-- url     : https://prove2.me/submissions/e7941745-dc5e-405e-819e-10c4f6f741d5

import Mathlib
import Definitions.Def_KernelRankLean_Defs

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
namespace IsSumOfProducts
theorem _root_.solution {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} {K : (∀ i, X i) → 𝕜} {N : ℕ} (hK : IsSumOfProducts K N)
    (g : ∀ i, Y i → X i) :
    IsSumOfProducts (fun y => K fun i => g i (y i)) N := by
  obtain ⟨f, hf⟩ := hK
  exact ⟨fun n i y => f n i (g i y), fun y => hf _⟩
end IsSumOfProducts
end KernelRank
