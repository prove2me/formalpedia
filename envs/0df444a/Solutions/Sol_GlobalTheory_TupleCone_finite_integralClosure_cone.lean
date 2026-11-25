-- Prove2me | solution 1 for GlobalTheory.TupleCone.finite_integralClosure_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:49.262643+00:00
-- url     : https://prove2.me/submissions/50549a64-7fc7-4e49-9687-1ddbe738fe02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_finite_integralClosure_of_essFiniteType_of_isReduced


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
variable (o t) [IsDedekindDomain o] [CharZero L] [Algebra.EssFiniteType o L] [Finite σ]
namespace GlobalTheory.TupleCone
theorem _root_.solution :
    Module.Finite (cone o t) (integralClosure (cone o t) L[X]) := by
  haveI : Algebra.FiniteType o (cone o t) := .adjoin_of_finite (Set.finite_range _)
  haveI : Algebra.EssFiniteType o L[X] := .comp o L _
  haveI : Algebra.EssFiniteType (cone o t) L[X] := .of_comp o _ _
  exact finite_integralClosure_of_essFiniteType_of_isReduced o _ _
end GlobalTheory.TupleCone
