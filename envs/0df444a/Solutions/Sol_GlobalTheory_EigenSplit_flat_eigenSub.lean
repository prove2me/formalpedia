-- Prove2me | solution 1 for GlobalTheory.EigenSplit.flat_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:39.435803+00:00
-- url     : https://prove2.me/submissions/79f484ae-8de3-4bbe-a71d-1d9e87f2cf9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

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
theorem _root_.solution [Module.Flat R N] (i : ι) : Module.Flat R (eigenSub ρ (σ i)) := by
  classical
  exact Module.Flat.of_retract _ _ (projTo_comp_subtype h ρ i)
end GlobalTheory.EigenSplit
