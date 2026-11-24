-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.fontaineTheta_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:57.889554+00:00
-- url     : https://prove2.me/submissions/d96828b9-8c85-4254-8786-3692488fe942

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi

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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : θ (mu ε) = 0 := by
  rw [mu, map_sub, map_one, fontaineTheta_teichmuller, hε, sub_self]
end GroundTheory.PAdicHodge.AInf
