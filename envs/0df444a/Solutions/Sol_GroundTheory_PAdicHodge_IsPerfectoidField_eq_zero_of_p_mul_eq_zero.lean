-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_p_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:59:12.195227+00:00
-- url     : https://prove2.me/submissions/4f4a665f-5522-44b3-b802-09eedee40b20

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
theorem _root_.solution {x : 𝕎𝒪♭} (h : (p : 𝕎𝒪♭) * x = 0) : x = 0 :=
  WittVector.eq_zero_of_p_mul_eq_zero x (by rwa [mul_comm])
end GroundTheory.PAdicHodge.IsPerfectoidField
