-- Prove2me | solution 1 for GlobalTheory.isGradedMap_lsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:46.312042+00:00
-- url     : https://prove2.me/submissions/e501e156-dc33-44d8-baa5-cedf8d8fecd3

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
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
namespace GlobalTheory
theorem _root_.solution (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] {p : MvPolynomial ι R}
    {d : ℤ} (hp : p ∈ polyGrading ι R d) :
    IsGradedMap ℳ (grShift ℳ d) (LinearMap.lsmul (MvPolynomial ι R) M p) :=
  fun _ _ h => grSMul_mem ℳ hp h
end GlobalTheory
