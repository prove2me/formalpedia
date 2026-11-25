-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isClopen_setOf_rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:52:34.007874+00:00
-- url     : https://prove2.me/submissions/ff2d02a5-242b-4c5b-b445-c272c9726829

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isLocallyConstant_rankAtStalk_eigenSub

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
  {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
include h
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Module.Projective R N] [Module.Finite R N] (r : ι → ℕ) :
    IsClopen {p : PrimeSpectrum R | ∀ i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i} := by
  rw [Set.ofPred_forall]
  exact isClopen_iInter_of_finite fun i =>
    (isLocallyConstant_rankAtStalk_eigenSub h ρ i).isClopen_fiber (r i)
end GlobalTheory.EigenSplit
