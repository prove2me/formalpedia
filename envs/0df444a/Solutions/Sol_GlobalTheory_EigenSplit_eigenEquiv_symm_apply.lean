-- Prove2me | solution 1 for GlobalTheory.EigenSplit.eigenEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:25:01.744801+00:00
-- url     : https://prove2.me/submissions/e9208690-42c5-47a3-93c2-ff638d6e259a

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
variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Fintype ι] (v : ∀ i, eigenSub ρ (σ i)) :
    (eigenEquiv h ρ).symm v = ∑ i, (v i : N) := by
  simp [eigenEquiv]
end GlobalTheory.EigenSplit
