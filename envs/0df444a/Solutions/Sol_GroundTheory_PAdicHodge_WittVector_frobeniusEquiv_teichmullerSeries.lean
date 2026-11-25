-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_teichmullerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:18:19.157141+00:00
-- url     : https://prove2.me/submissions/ce5e9f51-6e99-4054-881d-3ceea9ad9a17

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff
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
theorem _root_.solution (a : ℕ → R) :
    WittVector.frobeniusEquiv p R (WittVector.teichmullerSeries a) =
      WittVector.teichmullerSeries fun n => a n ^ p := by
  ext n
  rw [WittVector.frobeniusEquiv_coeff, WittVector.teichmullerSeries_coeff,
    WittVector.teichmullerSeries_coeff, ← pow_mul, ← pow_mul, mul_comm]
end WittVector
end GroundTheory.PAdicHodge
