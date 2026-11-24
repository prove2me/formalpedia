-- Prove2me | solution 1 for GlobalTheory.isGradedMap_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:50.693804+00:00
-- url     : https://prove2.me/submissions/a46b2cfe-98a9-4242-ac63-98400dc90eac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_isGradedMap_toSpanSingleton

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
theorem _root_.solution [Fintype κ] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    {g : κ → N} {d : κ → ℤ} (hg : ∀ k, g k ∈ 𝒩 (d k)) :
    IsGradedMap (grFree ι R d) 𝒩 (Fintype.linearCombination (MvPolynomial ι R) g) :=
  fun _ _ h => by
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ =>
      isGradedMap_toSpanSingleton 𝒩 (hg k) (mem_grPi.1 h k)
end GlobalTheory
