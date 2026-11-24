-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.fontaineTheta_mul_p_sub_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:16.487043+00:00
-- url     : https://prove2.me/submissions/219739b1-9b20-4f33-a7ae-48fdc04a2ff7

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
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {ϖ : 𝒪♭} {w : 𝕎𝒪♭}
    (h : PreTilt.untilt ϖ = p * θ w) : w * p - teichmuller p ϖ ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, fontaineTheta_teichmuller, h, mul_comm,
    sub_self]
end GroundTheory.PAdicHodge.IsPerfectoidField
