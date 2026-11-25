-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.xi_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:33.864109+00:00
-- url     : https://prove2.me/submissions/4282d232-0ff5-4051-ac53-c3b09349a274

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_mu
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_preTilt


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
theorem _root_.solution (ε : 𝒪♭) :
    AInf.xi (K := K) ε - ((φ).symm (AInf.mu ε)) ^ (p - 1) ∈ Ideal.span {(p : AInf K p)} := by
  haveI := IsPerfectoidField.isDomain_preTilt (K := K) p
  rw [mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply,
    AInf.frobeniusEquiv_symm_mu, AInf.xi]
  simp only [map_sub, map_sum, map_pow, map_one, WittVector.constantCoeff_apply,
    teichmuller_coeff_zero]
  set e := (_root_.frobeniusEquiv 𝒪♭ p).symm ε
  have h1 := geom_sum_mul e p
  have h2 : (e - 1) ^ p = e ^ p - 1 := by rw [sub_pow_char, one_pow]
  by_cases he : e - 1 = 0
  · rw [he, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), sub_zero, sub_eq_zero.1 he]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact CharP.cast_eq_zero _ p
  · rw [sub_eq_zero]
    apply mul_right_cancel₀ he
    rw [h1, ← h2, ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
end GroundTheory.PAdicHodge.ACris
