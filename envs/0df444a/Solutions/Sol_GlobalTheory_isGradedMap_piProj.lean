-- Prove2me | solution 1 for GlobalTheory.isGradedMap_piProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:34.962152+00:00
-- url     : https://prove2.me/submissions/949f06f6-ecd4-4609-9a2c-7a4579e298fe

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
variable (ι)
namespace GlobalTheory
theorem _root_.solution (ℳ : ∀ k, ℤ → Submodule R (M k)) (k : κ) :
    IsGradedMap (grPi ℳ) (ℳ k) (LinearMap.proj (R := MvPolynomial ι R) k) :=
  fun _ _ h => mem_grPi.1 h k
end GlobalTheory
