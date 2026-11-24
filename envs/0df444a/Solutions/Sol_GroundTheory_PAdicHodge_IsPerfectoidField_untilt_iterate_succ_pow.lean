-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.untilt_iterate_succ_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:25:03.67001+00:00
-- url     : https://prove2.me/submissions/64fc0d5f-ab09-4525-b6af-0a9dba7e0832

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
theorem _root_.solution (x : 𝒪♭) (n : ℕ) :
    PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n + 1] x) ^ p =
      PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x) := by
  rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]
end GroundTheory.PAdicHodge.IsPerfectoidField
