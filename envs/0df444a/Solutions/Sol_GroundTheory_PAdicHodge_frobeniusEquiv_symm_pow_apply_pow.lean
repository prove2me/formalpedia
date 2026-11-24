-- Prove2me | solution 1 for GroundTheory.PAdicHodge.frobeniusEquiv_symm_pow_apply_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:45:12.993986+00:00
-- url     : https://prove2.me/submissions/fde208a4-375a-48b0-92f6-f5194a9092e7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_pow_apply

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
variable [PerfectRing R p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p).symm ^ n) y ^ p ^ n = y := by
  rw [← frobeniusEquiv_pow_apply]
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingEquiv.apply_symm_apply, ih]
end GroundTheory.PAdicHodge
