-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.frobenius_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.89591+00:00
-- url     : https://prove2.me/submissions/4a98942e-a3cb-4f2c-9eac-c9ceea3db9cc

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
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (a : R) :
    frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]
end WittVector
end GroundTheory.PAdicHodge
