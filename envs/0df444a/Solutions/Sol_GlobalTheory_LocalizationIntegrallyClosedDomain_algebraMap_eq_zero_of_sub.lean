-- Prove2me | solution 1 for GlobalTheory.LocalizationIntegrallyClosedDomain.algebraMap_eq_zero_of_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:05.774101+00:00
-- url     : https://prove2.me/submissions/30168691-0d85-4519-a41f-d89414d3410f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationIsDomainIsIntegrallyClosedOfFinsetSu

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.LocalizationIntegrallyClosedDomain
variable {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]
namespace GlobalTheory.LocalizationIntegrallyClosedDomain
theorem _root_.solution (C : Subring B) (c : C)
    (h : algebraMap C (Localization.AtPrime (Q.comap C.subtype)) c = 0) :
    algebraMap B (Localization.AtPrime Q) (c : B) = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl] at h
  obtain ⟨⟨m, hm⟩, hmc⟩ := h
  rw [IsLocalization.map_eq_zero_iff Q.primeCompl]
  refine ⟨⟨(m : B), by exact hm⟩, ?_⟩
  simpa using congrArg Subtype.val hmc
end GlobalTheory.LocalizationIntegrallyClosedDomain
