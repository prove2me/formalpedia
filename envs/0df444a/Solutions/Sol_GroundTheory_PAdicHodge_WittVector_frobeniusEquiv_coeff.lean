-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.846071+00:00
-- url     : https://prove2.me/submissions/c7e3987e-652c-449c-a3ba-26f556b11059

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (x : WittVector p R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R x).coeff n = x.coeff n ^ p := by
  rw [WittVector.frobeniusEquiv_apply, coeff_frobenius_charP]
end WittVector
end GroundTheory.PAdicHodge
