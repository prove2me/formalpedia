-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:27.033154+00:00
-- url     : https://prove2.me/submissions/01aff1ed-20de-493e-afc0-de3dd48c2070

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_fontaineTheta_mul_p_sub_teichmuller
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_coeff_one_mul_p_sub_teichmuller

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
theorem _root_.solution {pflat : 𝒪♭}
    (h : PreTilt.untilt pflat = p) :
    RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by
  have h' : PreTilt.untilt pflat = p * θ 1 := by rw [map_one, mul_one, h]
  have := ker_fontaineTheta_eq_span (fontaineTheta_mul_p_sub_teichmuller h')
    (isUnit_coeff_one_mul_p_sub_teichmuller (by rw [map_one]; exact isUnit_one) h')
  rwa [one_mul] at this
end GroundTheory.PAdicHodge.IsPerfectoidField
