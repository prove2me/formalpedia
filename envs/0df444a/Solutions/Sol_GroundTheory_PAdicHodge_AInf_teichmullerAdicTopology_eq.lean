-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.teichmullerAdicTopology_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:06.338224+00:00
-- url     : https://prove2.me/submissions/33b79ded-c1c3-4f74-a3a8-60e5d0d06e04

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_teichmullerAdicTopology_le

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
theorem _root_.solution (ϖ ϖ' : 𝒪♭) (hϖ0 : ϖ ≠ 0) (hϖ1 : ‖ϖ‖ < 1) (hϖ0' : ϖ' ≠ 0)
    (hϖ1' : ‖ϖ'‖ < 1) :
    teichmullerAdicTopology (K := K) ϖ = teichmullerAdicTopology ϖ' :=
  le_antisymm (teichmullerAdicTopology_le ϖ ϖ' hϖ1 hϖ0') (teichmullerAdicTopology_le ϖ' ϖ hϖ1' hϖ0)
end GroundTheory.PAdicHodge.AInf
