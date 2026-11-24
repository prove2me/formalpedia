-- Prove2me | solution 1 for GlobalTheory.EigenSplit.IsSplitting.exponents_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:42.096193+00:00
-- url     : https://prove2.me/submissions/66b9855a-648c-4736-b450-a8be32fed0a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_exponents_eq_of_isDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
namespace GlobalTheory.EigenSplit
namespace IsSplitting
theorem _root_.solution [Nontrivial R] {σ : ι → O →+* R} (h : IsSplitting σ)
    (r s : ι → ℕ) (hrs : ∀ a, ∏ i, (X - C (σ i a)) ^ r i = ∏ i, (X - C (σ i a)) ^ s i) :
    r = s := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  refine exponents_eq_of_isDomain (h.map (Ideal.Quotient.mk m)).injective r s fun a => ?_
  have := congrArg (Polynomial.map (Ideal.Quotient.mk m)) (hrs a)
  simpa [Polynomial.map_prod] using this
end IsSplitting
end GlobalTheory.EigenSplit
