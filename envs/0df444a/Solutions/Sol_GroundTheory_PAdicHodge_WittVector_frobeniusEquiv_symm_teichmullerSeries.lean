-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_teichmullerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:44.669119+00:00
-- url     : https://prove2.me/submissions/a1ad6833-f65f-4c65-8274-e3663e66c7e3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_teichmullerSeries

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
theorem _root_.solution (a : ℕ → R) :
    (WittVector.frobeniusEquiv p R).symm (WittVector.teichmullerSeries a) =
      WittVector.teichmullerSeries fun n => (_root_.frobeniusEquiv R p).symm (a n) := by
  apply (WittVector.frobeniusEquiv p R).injective
  rw [RingEquiv.apply_symm_apply, WittVector.frobeniusEquiv_teichmullerSeries]
  simp only [frobeniusEquiv_symm_pow_p]
end WittVector
end GroundTheory.PAdicHodge
