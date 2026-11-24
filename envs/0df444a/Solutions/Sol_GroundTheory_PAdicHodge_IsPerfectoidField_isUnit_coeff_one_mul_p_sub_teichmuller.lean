-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_coeff_one_mul_p_sub_teichmuller
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:21.695159+00:00
-- url     : https://prove2.me/submissions/d2f33f38-bd6c-4e99-b5a1-f29f0cf0f688

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_eq_one
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
theorem _root_.solution {ϖ : 𝒪♭} {w : 𝕎𝒪♭} (hw : IsUnit (θ w))
    (h : PreTilt.untilt ϖ = p * θ w) : IsUnit ((w * p - teichmuller p ϖ).coeff 1) := by
  obtain ⟨s, hs⟩ := exists_eq_teichmuller_add_mul_p (-1 : 𝕎𝒪♭)
  have hneg : (-1 : 𝕎𝒪♭).coeff 0 = -1 := by
    have h0 := add_coeff_zero (-1 : 𝕎𝒪♭) 1
    rw [neg_add_cancel, one_coeff_zero, zero_coeff] at h0
    linear_combination -h0
  have e : teichmuller p (-ϖ) = teichmuller p ϖ * teichmuller p ((-1 : 𝕎𝒪♭).coeff 0) := by
    rw [hneg, ← map_mul, mul_neg_one]
  have key : w * p - teichmuller p ϖ = teichmuller p (-ϖ) + (w + teichmuller p ϖ * s) * p := by
    linear_combination teichmuller p ϖ * hs - e
  rw [key, coeff_one_teichmuller_add_mul_p]
  refine IsUnit.pow _ ((isUnit_iff_norm_untilt p).2 ?_)
  refine norm_eq_one_of_mk_eq p (c := θ w) ?_ (isUnit_iff_norm_eq_one.1 hw)
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt ϖ) = 0 := by
    rw [h, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [mk_untilt, add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero, map_add, map_mul,
    ← mk_untilt p ϖ, hmk, zero_mul, add_zero, mk_fontaineTheta]
end GroundTheory.PAdicHodge.IsPerfectoidField
