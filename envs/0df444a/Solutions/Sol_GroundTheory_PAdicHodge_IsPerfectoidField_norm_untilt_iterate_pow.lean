-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.norm_untilt_iterate_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:52.728307+00:00
-- url     : https://prove2.me/submissions/15c68d01-d2f7-49ed-b5f3-24e6da14d565

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
    ‖((PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x) : 𝒪) : K)‖ ^ p ^ n =
      ‖((PreTilt.untilt x : 𝒪) : K)‖ := by
  rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
end GroundTheory.PAdicHodge.IsPerfectoidField
