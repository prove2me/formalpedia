-- Prove2me | solution 1 for GlobalTheory.exists_bijective_toSpanSingleton_of_finite_maximalSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:02.43444+00:00
-- url     : https://prove2.me/submissions/ae48e9d0-6638-4179-8c97-2b72edebb827

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_free_of_invertible_of_finite_maximalSpectrum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Finite (MaximalSpectrum A)] [Module.Invertible A M] :
    ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e) := by
  obtain ⟨φ⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (free_of_invertible_of_finite_maximalSpectrum A M)
  refine ⟨φ.symm 1, ?_⟩
  have : LinearMap.toSpanSingleton A M (φ.symm 1) = φ.symm.toLinearMap := by ext; simp
  rw [this]
  exact φ.symm.bijective
end GlobalTheory
