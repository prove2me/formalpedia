-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.eq_zero_of_teichmuller_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:49.164578+00:00
-- url     : https://prove2.me/submissions/060054ff-d589-48dc-a68e-d4c65a1893bc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_wittVector_preTilt

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
theorem _root_.solution {ϖ : 𝒪♭} (hϖ : ϖ ≠ 0) {x : 𝕎𝒪♭}
    (h : teichmuller p ϖ * x = 0) : x = 0 := by
  have := isDomain_wittVector_preTilt K p
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hϖ ?_
  rw [← teichmuller_coeff_zero p ϖ, h0, zero_coeff]
end GroundTheory.PAdicHodge.IsPerfectoidField
