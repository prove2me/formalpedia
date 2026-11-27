-- Prove2me | solution 1 for GlobalTheory.isGradedMap_piSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:40.464045+00:00
-- url     : https://prove2.me/submissions/32660f1d-97c6-4e10-92c4-d9bacdc05ccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



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
theorem _root_.solution [DecidableEq κ] (ℳ : ∀ k, ℤ → Submodule R (M k)) (k : κ) :
    IsGradedMap (ℳ k) (grPi ℳ) (LinearMap.single (MvPolynomial ι R) M k) :=
  fun _ m hm => mem_grPi.2 fun j => by
    by_cases h : j = k
    · subst h; simpa using hm
    · rw [LinearMap.coe_single, Pi.single_eq_of_ne h]; exact zero_mem _
end GlobalTheory
