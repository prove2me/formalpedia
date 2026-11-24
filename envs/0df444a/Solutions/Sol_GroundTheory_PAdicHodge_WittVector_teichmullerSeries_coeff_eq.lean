-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.teichmullerSeries_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:45.700173+00:00
-- url     : https://prove2.me/submissions/bf850386-7203-4997-82e4-4a324c9f6e93

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff
import Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_symm_pow_apply_pow

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
namespace WittVector
theorem _root_.solution (x : WittVector p R) :
    WittVector.teichmullerSeries (fun n => ((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n)) =
      x := by
  ext n
  rw [WittVector.teichmullerSeries_coeff, frobeniusEquiv_symm_pow_apply_pow]
end WittVector
end GroundTheory.PAdicHodge
