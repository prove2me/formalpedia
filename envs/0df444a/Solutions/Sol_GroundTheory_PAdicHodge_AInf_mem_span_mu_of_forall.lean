-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.mem_span_mu_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:35.86853+00:00
-- url     : https://prove2.me/submissions/34f4c005-0f48-4a95-bd62-b54ef29f8b9c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobenius_pow_mu
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_natCast_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_kerThetaFrob
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_constantCoeff_mu
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_sub_one_dvd_coeff_zero
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_le_span_singleton_of_forall_mem_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {a : AInf K p}
    (ha : ∀ n : ℕ, θ ((φ ^ n) a) = 0) : a ∈ Ideal.span {mu ε} := by
  have hp0 := natCast_ne_zero hε hζ
  have hJ : kerThetaFrob K p ≤ Ideal.span {mu ε} := by
    refine le_span_singleton_of_forall_mem_eq (π := (p : AInf K p)) fun x hx => ?_
    rw [mem_kerThetaFrob] at hx
    obtain ⟨β, hβ⟩ := sub_one_dvd_coeff_zero hε hζ hx
    obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p (x - mu ε * teichmuller p β)
    have h0 : (x - mu ε * teichmuller p β).coeff 0 = 0 := by
      change _root_.WittVector.constantCoeff (x - mu ε * teichmuller p β) = 0
      rw [map_sub, map_mul, constantCoeff_mu, hβ]
      change _ - _ * (teichmuller p β).coeff 0 = 0
      rw [teichmuller_coeff_zero, sub_self]
    rw [h0, teichmuller_zero, zero_add] at hv
    have hxv : x = teichmuller p β * mu ε + v * p := by linear_combination hv
    refine ⟨teichmuller p β, v, ?_, hxv⟩
    rw [mem_kerThetaFrob]
    intro n
    have h := hx n
    rw [hxv, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
      fontaineTheta_frobenius_pow_mu hε, mul_zero, zero_add, map_natCast, map_natCast,
      mul_eq_zero] at h
    exact h.resolve_right hp0
  exact hJ (mem_kerThetaFrob.2 ha)
end GroundTheory.PAdicHodge.AInf
