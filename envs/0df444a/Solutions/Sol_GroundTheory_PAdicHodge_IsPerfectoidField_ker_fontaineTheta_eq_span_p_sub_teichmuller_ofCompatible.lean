-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:05:21.842926+00:00
-- url     : https://prove2.me/submissions/5415cc9f-5e71-4ba6-8bcb-1e29bc92af72

import Mathlib
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_ker_fontaineTheta_eq_span_p_sub_teichmuller
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible
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
theorem solution (y : ℕ → 𝒪)
    (hy : ∀ n, y (n + 1) ^ p = y n) (h0 : y 0 = p) :
    RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p (ofCompatible p y hy)} := by
  have h : PreTilt.untilt (ofCompatible p y hy) = p := by
    rw [IsPerfectoidField.untilt_ofCompatible]; exact h0
  exact IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller h
