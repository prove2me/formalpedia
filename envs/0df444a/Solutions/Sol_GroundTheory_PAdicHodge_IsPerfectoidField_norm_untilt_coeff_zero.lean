-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.norm_untilt_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:13.914265+00:00
-- url     : https://prove2.me/submissions/2a114ab8-4211-411d-b6d0-49cc1a16d704

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_coeff_zero_add_eq_zero

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
theorem _root_.solution {ξ v : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) :
    ‖((PreTilt.untilt (ξ.coeff 0) : 𝒪) : K)‖ = ‖((θ v : 𝒪) : K)‖ * ‖(p : K)‖ := by
  have h := congrArg (fun z : 𝒪 => (z : K)) (untilt_coeff_zero_add_eq_zero hξ hv)
  simp only [AddMemClass.coe_add, Subring.coe_mul, ZeroMemClass.coe_zero] at h
  have : ((PreTilt.untilt (ξ.coeff 0) : 𝒪) : K) = -(((θ v : 𝒪) : K) * (((p : 𝒪)) : K)) := by
    linear_combination h
  rw [this, norm_neg, norm_mul]
  simp
end GroundTheory.PAdicHodge.IsPerfectoidField
