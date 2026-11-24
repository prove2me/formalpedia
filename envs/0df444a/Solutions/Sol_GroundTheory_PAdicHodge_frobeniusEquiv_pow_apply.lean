-- Prove2me | solution 1 for GroundTheory.PAdicHodge.frobeniusEquiv_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:20.804728+00:00
-- url     : https://prove2.me/submissions/23ee28fa-f215-47ca-9dd1-cc0b1a44c9fa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow

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
    ((_root_.frobeniusEquiv R p) ^ n) y = y ^ p ^ n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih, _root_.frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      ← pow_succ']
end GroundTheory.PAdicHodge
