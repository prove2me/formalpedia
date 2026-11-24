-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.mem_kerThetaFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:06.795039+00:00
-- url     : https://prove2.me/submissions/63741af6-fb69-47d0-b9b7-986b4a9aa0e3

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {a : AInf K p} : a ∈ kerThetaFrob K p ↔ ∀ n : ℕ, θ ((φ ^ n) a) = 0 := by
  simp only [kerThetaFrob, Ideal.mem_iInf, RingHom.mem_ker, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply]
end GroundTheory.PAdicHodge.AInf
