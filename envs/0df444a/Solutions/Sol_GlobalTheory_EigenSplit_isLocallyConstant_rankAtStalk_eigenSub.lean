-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isLocallyConstant_rankAtStalk_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:41.855372+00:00
-- url     : https://prove2.me/submissions/406a5ba5-d353-4d15-97e2-ee9e6f46e4ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_finite_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_projective_eigenSub

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
omit [Fintype ι]
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Module.Projective R N] [Module.Finite R N]
    (i : ι) : IsLocallyConstant (Module.rankAtStalk (R := R) (eigenSub ρ (σ i))) :=
  have := finite_eigenSub h ρ i
  have := projective_eigenSub h ρ i
  have := Module.finitePresentation_of_projective R (eigenSub ρ (σ i))
  Module.isLocallyConstant_rankAtStalk
end GlobalTheory.EigenSplit
