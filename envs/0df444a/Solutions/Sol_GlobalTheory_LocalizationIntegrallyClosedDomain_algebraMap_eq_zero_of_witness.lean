-- Prove2me | solution 1 for GlobalTheory.LocalizationIntegrallyClosedDomain.algebraMap_eq_zero_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:49.292719+00:00
-- url     : https://prove2.me/submissions/e435c7ac-3b93-414d-ada9-b6f2528158e4

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
theorem _root_.solution (C : Subring B) (u e : C) (hu : (u : B) ∉ Q)
    (h : u * e = 0) :
    algebraMap C (Localization.AtPrime (Q.comap C.subtype)) e = 0 := by
  rw [IsLocalization.map_eq_zero_iff (Q.comap C.subtype).primeCompl]
  exact ⟨⟨u, by exact hu⟩, h⟩
end GlobalTheory.LocalizationIntegrallyClosedDomain
