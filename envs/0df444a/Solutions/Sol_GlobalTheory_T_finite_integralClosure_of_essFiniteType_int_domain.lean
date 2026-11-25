-- Prove2me | solution 1 for GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:38:34.213145+00:00
-- url     : https://prove2.me/submissions/a058420e-2376-47d4-89a6-424f42abd6f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteIntegralClosureOfEssFiniteTypeIntDomainStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
end _root_.GlobalTheory.T
