-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittVector.teichmullerSeries_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:19.95431+00:00
-- url     : https://prove2.me/submissions/a4fb5c16-762e-4dc9-a250-c0a36dc02c87

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
omit hp [CharP R p]
namespace GroundTheory.PAdicHodge
namespace WittVector
theorem _root_.solution (a : ℕ → R) (n : ℕ) :
    (WittVector.teichmullerSeries (p := p) a).coeff n = a n ^ p ^ n := rfl
end WittVector
end GroundTheory.PAdicHodge
