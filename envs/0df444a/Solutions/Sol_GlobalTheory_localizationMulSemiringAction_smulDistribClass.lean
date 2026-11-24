-- Prove2me | solution 1 for GlobalTheory.localizationMulSemiringAction_smulDistribClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:07.275747+00:00
-- url     : https://prove2.me/submissions/a586d65f-da11-4fa5-b9e2-92dffeb2c5aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_localizationMulSemiringAction_smul_algebraMap

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
variable (G : Type*) [Group G]
variable {A : Type*} [CommRing A] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution (U : Submonoid A)
    (hU : ∀ (g : G), ∀ u ∈ U, g • u ∈ U) (A' : Type*) [CommRing A'] [Algebra A A']
    [IsLocalization U A'] :
    letI := localizationMulSemiringAction G U hU A'
    SMulDistribClass G A A' :=
  letI := localizationMulSemiringAction G U hU A'
  ⟨fun g a x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul',
      localizationMulSemiringAction_smul_algebraMap]⟩
end GlobalTheory
