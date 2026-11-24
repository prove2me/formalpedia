-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_pow_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:14.30832+00:00
-- url     : https://prove2.me/submissions/02351e7c-e9b9-44e8-9685-9a6761053e97

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
theorem _root_.solution (a : R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R ^ n) (teichmuller p a) = teichmuller p (a ^ p ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, WittVector.frobeniusEquiv_teichmuller, ← pow_mul,
      ← pow_succ]
end WittVector
end GroundTheory.PAdicHodge
