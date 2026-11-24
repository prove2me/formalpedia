-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:36.478828+00:00
-- url     : https://prove2.me/submissions/3cf41628-563a-4736-8fc4-4fe8109322fb

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_teichmuller

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (a : R) :
    (WittVector.frobeniusEquiv p R).symm (teichmuller p a) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm a) := by
  apply (WittVector.frobeniusEquiv p R).injective
  rw [RingEquiv.apply_symm_apply, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]
end WittVector
end GroundTheory.PAdicHodge
