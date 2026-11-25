-- Prove2me | solution 1 for GroundTheory.PAdicHodge.WittTilt.exists_eq_pow_mul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:08.826437+00:00
-- url     : https://prove2.me/submissions/2054dc0a-f832-4cb3-8174-c95e7254bcb9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonApprox
import Theorems.Thm_GroundTheory_PAdicHodge_ACris_span_p_pow_map


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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p
namespace GroundTheory.PAdicHodge.WittTilt
theorem _root_.solution {c₁ c₂ : ACrisZero K p} {N : ℕ}
    (h : algebraMap _ (ACris K p) c₁ - algebraMap _ (ACris K p) c₂ ∈
      Ideal.span {(p : ACris K p) ^ N}) :
    ∃ z : ACrisZero K p, c₁ - c₂ = (p : ACrisZero K p) ^ N * z := by
  rw [← Ideal.span_singleton_pow, ← span_p_pow_map, ← map_sub,
    ← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _), RingHom.mem_ker] at h
  have h2 : Ideal.Quotient.mk (Ideal.span {(p : ACrisZero K p)} ^ N) (c₁ - c₂) = 0 := by
    rw [← _root_.AdicCompletion.evalₐ_of]
    exact h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact h2
end GroundTheory.PAdicHodge.WittTilt
