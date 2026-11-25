-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.exists_mu_pow_eq_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:06.771801+00:00
-- url     : https://prove2.me/submissions/89f07e73-5607-4859-8a7a-b6c50b006b71

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_p_pow_p_mem
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_xi_sub_pow_mem
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_xi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_mu_eq_xi_mul


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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ∃ c : ACrisZero K p,
      (algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε)) ^ (p - 1) = (p : ACrisZero K p) * c ∧
        c ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (xi_sub_pow_mem (K := K) ε)
  have hξ : AInf.xi ε ∈ RingHom.ker θ := RingHom.mem_ker.2 (AInf.fontaineTheta_xi hε hζ)
  set ξ := AInf.xi (K := K) ε
  set v := (φ).symm (AInf.mu ε)
  have hμ : AInf.mu ε = ξ * v := AInf.mu_eq_xi_mul ε
  have hW : AInf.mu ε ^ (p - 1) = ξ ^ p - (p : AInf K p) * (a * ξ ^ (p - 1)) := by
    have hv : v ^ (p - 1) = ξ - a * p := by rw [ha]; ring
    have hp1 : ξ ^ p = ξ ^ (p - 1) * ξ := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
    rw [hμ, mul_pow, hv, hp1]
    ring
  set D : ACrisZero K p := ⟨dpow p ξ, dpow_mem hξ p⟩ with hD
  set B : ACrisZero K p := algebraMap (AInf K p) (ACrisZero K p) (a * ξ ^ (p - 1)) with hB
  have hξp : (algebraMap (AInf K p) (ACrisZero K p) ξ) ^ p = (p.factorial : ACrisZero K p) * D := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_mul, SubringClass.coe_natCast,
      Subalgebra.coe_algebraMap, hD]
    rw [factorial_mul_dpow]
  refine ⟨((p - 1).factorial : ACrisZero K p) * D - B, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_sub, SubringClass.coe_natCast,
      Subalgebra.coe_algebraMap, hD, hB]
    rw [← map_pow, hW, map_sub, map_pow, ← factorial_mul_dpow, map_mul, map_natCast,
      ← Nat.mul_factorial_pred hp.out.ne_zero, Nat.cast_mul]
    ring
  · have hDp : D ^ p ∈ Ideal.span {(p : ACrisZero K p)} := dpow_p_pow_p_mem hξ
    have hBp : B ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by
      have e : B ^ p = algebraMap (AInf K p) (ACrisZero K p) a ^ p *
          ((p.factorial : ACrisZero K p) * D) ^ (p - 1) := by
        rw [hB, ← hξp, map_mul, map_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (p - 1) p]
      rw [e]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ _ (Nat.sub_pos_of_lt hp.out.one_lt))
      rw [← Nat.mul_factorial_pred hp.out.ne_zero, Nat.cast_mul, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (((p - 1).factorial : ACrisZero K p) * D) (-B)
    rw [sub_eq_add_neg, hr]
    refine add_mem (add_mem ?_ ?_) ?_
    · rw [mul_pow]; exact Ideal.mul_mem_left _ _ hDp
    · rw [show (-B) ^ p = (-1) ^ p * B ^ p by ring]; exact Ideal.mul_mem_left _ _ hBp
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
end GroundTheory.PAdicHodge.ACris
