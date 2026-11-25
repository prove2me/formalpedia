-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:18.398186+00:00
-- url     : https://prove2.me/submissions/1fadab6c-8e09-451a-bf91-3fdd60d2d76e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_coeff

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
theorem _root_.solution (x : WittVector p R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm x).coeff n = (_root_.frobeniusEquiv R p).symm (x.coeff n) := by
  conv_rhs => rw [← RingEquiv.apply_symm_apply (WittVector.frobeniusEquiv p R) x,
    WittVector.frobeniusEquiv_coeff]
  rw [← frobenius_def, frobeniusEquiv_symm_apply_frobenius]
end WittVector
end GroundTheory.PAdicHodge
