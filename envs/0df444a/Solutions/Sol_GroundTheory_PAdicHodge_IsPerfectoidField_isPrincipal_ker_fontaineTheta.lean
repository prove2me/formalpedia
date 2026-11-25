-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isPrincipal_ker_fontaineTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:53.69075+00:00
-- url     : https://prove2.me/submissions/0f49a545-ba56-44a2-8487-589cd831a160

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mem_ker_fontaineTheta_isUnit_coeff_one

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
variable (K p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution : (RingHom.ker θ).IsPrincipal := by
  obtain ⟨ξ, hξ, h1⟩ := exists_mem_ker_fontaineTheta_isUnit_coeff_one K p
  exact ⟨⟨ξ, ker_fontaineTheta_eq_span hξ h1⟩⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
