-- Prove2me | solution 1 for GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:40:11.076642+00:00
-- url     : https://prove2.me/submissions/1f8dd51c-6b0d-4a20-8514-1ceb6ec41fc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_stalk_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
universe u
open GlobalTheory
open AlgebraicGeometry
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) : IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  have := (hY (f x)).1
  have := (hY (f x)).2
  isDomain_and_isIntegrallyClosed_stalk_of_smooth f x
end GlobalTheory
