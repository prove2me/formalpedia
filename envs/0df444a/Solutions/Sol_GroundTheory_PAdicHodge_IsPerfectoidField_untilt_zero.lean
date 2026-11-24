-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.untilt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:08.837677+00:00
-- url     : https://prove2.me/submissions/a3c983fe-0fe0-47f3-b0ff-bcfea11437c5

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta

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
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : PreTilt.untilt (0 : 𝒪♭) = 0 :=
  Perfection.teichmuller_zero
end GroundTheory.PAdicHodge.IsPerfectoidField
