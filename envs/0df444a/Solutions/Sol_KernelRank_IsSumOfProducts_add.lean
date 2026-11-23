-- Prove2me | solution 1 for KernelRank.IsSumOfProducts.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:20.356802+00:00
-- url     : https://prove2.me/submissions/87817947-0091-4e9d-b75b-135d42dc70ec

import Mathlib
import Definitions.Def_KernelRankLean_Defs
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
namespace IsSumOfProducts
theorem _root_.solution {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} {K₁ K₂ : (∀ i, X i) → 𝕜} {N₁ N₂ : ℕ}
    (h₁ : IsSumOfProducts K₁ N₁) (h₂ : IsSumOfProducts K₂ N₂) :
    IsSumOfProducts (fun x => K₁ x + K₂ x) (N₁ + N₂) := by
  let K : Bool → (∀ i, X i) → 𝕜 := fun b => cond b K₁ K₂
  let N : Bool → ℕ := fun b => cond b N₁ N₂
  have hsum := IsSumOfProducts.finsetSum (α := Bool) (K := K) (N := N) fun b => by
    cases b <;> assumption
  simpa [K, N, add_comm] using hsum
end IsSumOfProducts
end KernelRank
