-- Prove2me | solution 1 for GlobalTheory.ShiftVariables.shiftVars_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:07.189258+00:00
-- url     : https://prove2.me/submissions/d4d5f476-fd7e-439f-ad05-d19b3f63c688

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ShiftVariables
namespace GlobalTheory.ShiftVariables
theorem _root_.solution (ι k : Type) [CommRing k] (i : ι) :
    shiftVars ι k (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + 1) (MvPolynomial.X i) = _
  simp
end GlobalTheory.ShiftVariables
