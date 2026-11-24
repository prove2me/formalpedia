-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.norm_fontaineTheta_eq_one_of_isUnit_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:23.478411+00:00
-- url     : https://prove2.me/submissions/1d217a57-e439-4dbc-bd23-7b847a0653e0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_eq_one_of_mk_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_untilt

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
theorem _root_.solution {ξ v : 𝕎𝒪♭}
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) (h1 : IsUnit (ξ.coeff 1)) :
    ‖((θ v : 𝒪) : K)‖ = 1 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := congrArg (fun w : 𝕎𝒪♭ => w.coeff 1) hv
  rw [coeff_one_teichmuller_add_mul_p] at h
  rw [h] at h1
  have hv0 : IsUnit (v.coeff 0) := (isUnit_pow_iff hp0).1 h1
  refine norm_eq_one_of_mk_eq p (c := PreTilt.untilt (v.coeff 0)) ?_
    (isUnit_iff_norm_untilt p |>.1 hv0)
  rw [mk_fontaineTheta, mk_untilt]
end GroundTheory.PAdicHodge.IsPerfectoidField
