-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_mem_ker_isUnit_coeff_one_of_untilt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:32.537895+00:00
-- url     : https://prove2.me/submissions/189f1d29-f26b-4c0f-b034-ce7c16f3bd6e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_fontaineTheta_mul_p_sub_teichmuller
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_coeff_one_mul_p_sub_teichmuller
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_fontaineTheta


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
theorem _root_.solution {ϖ : 𝒪♭} {u : 𝒪} (hu : IsUnit u)
    (h : PreTilt.untilt ϖ = p * u) :
    ∃ ξ ∈ RingHom.ker θ, IsUnit (ξ.coeff 1) := by
  obtain ⟨w, rfl⟩ := surjective_fontaineTheta (K := K) p u
  exact ⟨_, fontaineTheta_mul_p_sub_teichmuller h, isUnit_coeff_one_mul_p_sub_teichmuller hu h⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
