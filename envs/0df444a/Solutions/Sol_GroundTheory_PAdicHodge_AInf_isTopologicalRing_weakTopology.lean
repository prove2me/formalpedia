-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.isTopologicalRing_weakTopology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:53.662816+00:00
-- url     : https://prove2.me/submissions/64a73030-1023-44b2-988d-fc8dd4faad30

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_weakTopology_eq_adicTopology

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
theorem _root_.solution (ϖ : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) :
    @IsTopologicalRing (AInf K p) (weakTopology K p) _ := by
  rw [weakTopology_eq_adicTopology ϖ hϖ0 hϖ1]
  exact (Ideal.span {(p : AInf K p), teichmuller p ϖ}).ringFilterBasis.isTopologicalRing
end GroundTheory.PAdicHodge.AInf
