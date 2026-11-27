-- Prove2me | solution 2 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_ker_fontaineTheta_eq_span_p_sub_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:50.617333+00:00
-- url     : https://prove2.me/submissions/de369bad-47c1-44e6-ad2f-c73b3f15563d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span_p_sub_teichmuller
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_untilt_eq_p

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
theorem _root_.solution [IsAlgClosed K] :
    ∃ pflat : 𝒪♭, PreTilt.untilt pflat = p ∧
      RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by
  obtain ⟨pflat, h⟩ := exists_untilt_eq_p K p
  exact ⟨pflat, h, ker_fontaineTheta_eq_span_p_sub_teichmuller h⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
