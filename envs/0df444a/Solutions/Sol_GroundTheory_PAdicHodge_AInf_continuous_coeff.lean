-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.continuous_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:25.256276+00:00
-- url     : https://prove2.me/submissions/2ca7627c-3916-4cdc-88f6-6a4978015e18

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology

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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (i : ℕ) :
    @Continuous (AInf K p) 𝒪♭ (weakTopology K p) _ fun y => y.coeff i := by
  let := weakTopology K p
  exact (continuous_apply i).comp continuous_induced_dom
end GroundTheory.PAdicHodge.AInf
