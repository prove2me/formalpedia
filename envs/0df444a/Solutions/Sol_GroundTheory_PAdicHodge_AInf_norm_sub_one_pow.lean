-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.norm_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:47:58.318789+00:00
-- url     : https://prove2.me/submissions/dc161b55-47a5-4822-acb2-209c127bbd10

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_eq_norm_p
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_eq_of_mk_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_iterate_pow


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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ‖ε - 1‖ ^ (p - 1) = ‖(p : K)‖ ^ p := by
  set z : 𝒪 := PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm^[2] ε) with hz
  have hz2 : z ^ p ^ (1 + 1) = 1 := by
    rw [hz, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, hε]
  have hz1 : ¬ z ^ p ^ 1 = 1 := by
    intro h
    apply hζ
    rw [← h, hz, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow
      ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) 1]
    rfl
  have hz2K : (z : K) ^ p ^ (1 + 1) = 1 := by
    rw [← SubmonoidClass.coe_pow, hz2, OneMemClass.coe_one]
  have hz1K : ¬ (z : K) ^ p ^ 1 = 1 := by
    rw [← SubmonoidClass.coe_pow]
    exact fun h => hz1 (Subtype.ext (by rw [h, OneMemClass.coe_one]))
  have hprim : IsPrimitiveRoot (z : K) (p ^ (1 + 1)) := by
    rw [← orderOf_eq_prime_pow hz1K hz2K]
    exact IsPrimitiveRoot.orderOf _
  have hnorm := norm_sub_one_pow_eq_norm_p hprim
  set a := ‖(z : K) - 1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 (sub_ne_zero.2 fun h => hz1K (by rw [h, one_pow]))
  have ha1 : a ≤ 1 := by
    have := mem_normInteger.1 (z - 1).2
    rwa [AddSubgroupClass.coe_sub, OneMemClass.coe_one] at this
  have hp1 : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  have hp2 : 1 < p ^ 1 * (p - 1) := by
    have := hp.out.two_le
    rw [pow_one]
    nlinarith [Nat.sub_add_cancel hp.out.one_le]
  have hpa : ‖(p : K)‖ < a := by
    have ha1' : a < 1 := lt_of_le_of_ne ha1 fun h => by
      rw [h, one_pow] at hnorm; linarith
    rw [← hnorm]
    exact pow_lt_self_of_lt_one₀ ha0 ha1' hp2
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})
      (PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm^[2] (ε - 1))) =
        Ideal.Quotient.mk _ (z - 1) := by
    rw [← coeff_eq_mk_untilt (ε - 1) 2, map_sub, map_one, coeff_eq_mk_untilt ε 2, map_sub, map_one]
  have hb := IsPerfectoidField.norm_eq_of_mk_eq p hmk (by
    rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one]; exact hpa)
  rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one] at hb
  have hε1 : ‖ε - 1‖ = a ^ p ^ 2 := by
    rw [preTilt_norm_def, ← norm_untilt_iterate_pow (ε - 1) 2, hb]
  rw [hε1, ← pow_mul, ← hnorm, ← pow_mul]
  congr 1
  ring
end GroundTheory.PAdicHodge.AInf
