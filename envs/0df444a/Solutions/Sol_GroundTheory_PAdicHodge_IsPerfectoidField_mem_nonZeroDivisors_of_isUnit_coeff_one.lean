-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.mem_nonZeroDivisors_of_isUnit_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:50:54.844242+00:00
-- url     : https://prove2.me/submissions/d412be3a-f4bf-4ea4-a9a8-4f693740aa4f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_wittVector_preTilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_preTilt


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
theorem _root_.solution {ξ : 𝕎𝒪♭} (h1 : IsUnit (ξ.coeff 1)) :
    ξ ∈ nonZeroDivisors 𝕎𝒪♭ := by
  have := isDomain_preTilt (K := K) p
  have := isDomain_wittVector_preTilt K p
  refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
  rw [h, zero_coeff] at h1
  exact not_isUnit_zero h1
end GroundTheory.PAdicHodge.IsPerfectoidField
