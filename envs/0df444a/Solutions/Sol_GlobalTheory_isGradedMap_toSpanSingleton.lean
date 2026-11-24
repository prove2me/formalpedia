-- Prove2me | solution 1 for GlobalTheory.isGradedMap_toSpanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:24.053912+00:00
-- url     : https://prove2.me/submissions/7fbb183c-4974-4fb6-bc9f-050bdfeb9523

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
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
namespace GlobalTheory
theorem _root_.solution (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {m : M} {d : ℤ}
    (hm : m ∈ ℳ d) : IsGradedMap (grShift (polyGrading ι R) (-d)) ℳ
      (LinearMap.toSpanSingleton (MvPolynomial ι R) M m) :=
  fun _ _ h => by simpa using grSMul_mem ℳ h hm
end GlobalTheory
