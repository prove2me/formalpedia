-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:30.080467+00:00
-- url     : https://prove2.me/submissions/90dd2fce-bd32-4b12-8fcd-9ac9a82e230b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R] {κ : Type*}
  {M : κ → Type*} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
namespace GlobalTheory
namespace IsGradedMap
theorem _root_.solution {𝒩 : ℤ → Submodule R N} {ℳ : ∀ k, ℤ → Submodule R (M k)}
    {f : ∀ k, N →ₗ[MvPolynomial ι R] M k} (hf : ∀ k, IsGradedMap 𝒩 (ℳ k) (f k)) :
    IsGradedMap 𝒩 (grPi ℳ) (LinearMap.pi f) := fun _ _ h => mem_grPi.2 fun k => hf k h
end IsGradedMap
end GlobalTheory
