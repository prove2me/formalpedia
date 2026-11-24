-- Prove2me | solution 1 for GlobalTheory.EigenSplit.finrank_eq_of_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:19.027795+00:00
-- url     : https://prove2.me/submissions/df20cf3e-9141-488a-863c-04ba60cdf659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_IsSplitting_exponents_eq
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
variable {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
  [Module.Free R N] [Module.Finite R N]
include h
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Nontrivial R] (hfree : ∀ i, Module.Free R (eigenSub ρ (σ i)))
    (r : ι → ℕ) (hr : ∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) (i : ι) :
    Module.finrank R (eigenSub ρ (σ i)) = r i :=
  congrFun (h.exponents_eq (fun i => Module.finrank R (eigenSub ρ (σ i))) r
    fun a => by rw [← charpoly_eq_prod h ρ hfree, hr]) i
end GlobalTheory.EigenSplit
