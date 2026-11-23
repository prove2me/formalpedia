-- Prove2me | solution 1 for KernelRank.IsSumOfProducts.finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:48:58.196451+00:00
-- url     : https://prove2.me/submissions/e9870d6a-a546-4d87-99b7-a92777b4fb02

import Mathlib
import Definitions.Def_KernelRankLean_Defs

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
namespace IsSumOfProducts
theorem _root_.solution {𝕜 : Type*} [CommSemiring 𝕜] {ι α : Type*} [Fintype ι]
    [Fintype α] {X : ι → Type*} {K : α → (∀ i, X i) → 𝕜} {N : α → ℕ}
    (hK : ∀ a, IsSumOfProducts (K a) (N a)) :
    IsSumOfProducts (fun x => ∑ a, K a x) (∑ a, N a) := by
  classical
  choose f hf using hK
  let e : (Σ a, Fin (N a)) ≃ Fin (∑ a, N a) := Fintype.equivOfCardEq (by simp)
  refine ⟨fun n i x => f (e.symm n).1 (e.symm n).2 i x, fun x => ?_⟩
  simp_rw [hf]
  exact ((e.symm.sum_comp (fun p : Σ a, Fin (N a) => ∏ i, f p.1 p.2 i (x i))).trans
    (Fintype.sum_sigma _)).symm
end IsSumOfProducts
end KernelRank
