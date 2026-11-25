-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:34.912722+00:00
-- url     : https://prove2.me/submissions/0cde67dc-1313-4b42-a483-a70c592fb280

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mem_ker_isUnit_coeff_one_of_untilt_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_untilt_eq_p_mul_unit

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
theorem _root_.solution :
    ∃ ξ ∈ RingHom.ker θ, IsUnit (ξ.coeff 1) := by
  obtain ⟨ϖ, u, hu, h⟩ := exists_untilt_eq_p_mul_unit K p
  exact exists_mem_ker_isUnit_coeff_one_of_untilt_eq hu h
end GroundTheory.PAdicHodge.IsPerfectoidField
