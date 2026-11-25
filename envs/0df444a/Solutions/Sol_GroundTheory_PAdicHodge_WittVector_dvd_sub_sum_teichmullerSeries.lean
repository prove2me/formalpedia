-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.dvd_sub_sum_teichmullerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:02.321033+00:00
-- url     : https://prove2.me/submissions/2d47c9ee-e8e7-4bc0-9f34-f4a33d496afa

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_WittVector_eq_teichmullerSeries_iff

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
theorem _root_.solution (a : ℕ → R) (n : ℕ) :
    (p : WittVector p R) ^ (n + 1) ∣ WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i :=
  (WittVector.eq_teichmullerSeries_iff a _).1 rfl n
end WittVector
end GroundTheory.PAdicHodge
