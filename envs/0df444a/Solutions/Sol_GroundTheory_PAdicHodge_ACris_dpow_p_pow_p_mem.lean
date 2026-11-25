-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.dpow_p_pow_p_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:30.542559+00:00
-- url     : https://prove2.me/submissions/7c40dda7-842f-4556-acd5-77b1ded8b1f7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_p_pow_succ

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
theorem _root_.solution {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    (⟨dpow p x, dpow_mem hx p⟩ : ACrisZero K p) ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by
  have hp2 := hp.out.two_le
  have hdvd : p ∣ ∏ i ∈ Finset.range (p - 1), ((i + 2) * p).choose p := by
    have hmem : p - 2 ∈ Finset.range (p - 1) := Finset.mem_range.2 (by omega)
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    have e : (p - 2 + 2) * p = p ^ 2 := by rw [Nat.sub_add_cancel hp2, sq]
    rw [e]
    refine (Nat.Prime.dvd_choose_pow_iff hp.out).2 ⟨hp.out.ne_zero, fun h => ?_⟩
    nlinarith
  obtain ⟨N, hN⟩ := hdvd
  have h := dpow_p_pow_succ (K := K) x (p - 1)
  rw [Nat.sub_add_cancel hp.out.one_le, hN] at h
  rw [Ideal.mem_span_singleton']
  refine ⟨(N : ACrisZero K p) * ⟨dpow (p * p) x, dpow_mem hx _⟩, Subtype.ext ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
  rw [h, Nat.cast_mul]
  ring
end GroundTheory.PAdicHodge.ACris
