-- Prove2me | solution 1 for GlobalTheory.EigenSplit.free_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:47:30.501811+00:00
-- url     : https://prove2.me/submissions/4d9b7814-3260-4ad1-94bb-fe2761118a46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_finite_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_flat_eigenSub

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
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']
variable {σ : ι → O →+* R} (h : IsSplitting σ) {ρ : O →+* Module.End R N}
  {ρ' : O →+* Module.End R N'} {ρ'' : O →+* Module.End R N''}
include h
variable (ρ)
namespace GlobalTheory.EigenSplit
theorem _root_.solution [IsLocalRing R] [Module.Finite R N] [Module.Flat R N] (i : ι) :
    Module.Free R (eigenSub ρ (σ i)) :=
  have := finite_eigenSub h ρ i
  have := flat_eigenSub h ρ i
  Module.free_of_flat_of_isLocalRing
end GlobalTheory.EigenSplit
