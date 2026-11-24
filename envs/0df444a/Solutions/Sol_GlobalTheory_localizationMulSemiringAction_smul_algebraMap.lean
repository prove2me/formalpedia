-- Prove2me | solution 1 for GlobalTheory.localizationMulSemiringAction_smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:03.576531+00:00
-- url     : https://prove2.me/submissions/cd7bb9c1-41b8-44a8-a643-bbaeee03aa56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

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
    [IsLocalization U A'] (g : G) (a : A) :
    letI := localizationMulSemiringAction G U hU A'
    g • algebraMap A A' a = algebraMap A A' (g • a) :=
  IsLocalization.map_eq _ a
end GlobalTheory
