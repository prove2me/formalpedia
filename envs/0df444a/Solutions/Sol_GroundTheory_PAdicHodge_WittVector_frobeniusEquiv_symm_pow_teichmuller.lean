-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_pow_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:46:37.137798+00:00
-- url     : https://prove2.me/submissions/6995f178-1d4c-42f5-839a-ae659d57067d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_symm_teichmuller

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
theorem _root_.solution (a : R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm ^ n) (teichmuller p a) =
      teichmuller p (((_root_.frobeniusEquiv R p).symm ^ n) a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_symm_teichmuller, pow_succ',
      RingAut.mul_apply]
end WittVector
end GroundTheory.PAdicHodge
