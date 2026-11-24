-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.exists_norm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:34:01.521628+00:00
-- url     : https://prove2.me/submissions/7ac8e4eb-926c-4af7-bee8-79e170122782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
import Theorems.Thm_GlobalTheory_PadicUnitBall_norm_lt_one_of_mem_maximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {κ : FractionRing V →+* PadicAlgCl p}
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∀ x ∈ maximalIdeal V ^ n,
      ‖κ (algebraMap V (FractionRing V) x)‖ ≤ r ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨‖κ (algebraMap V (FractionRing V) ϖ)‖, norm_nonneg _,
    norm_lt_one_of_mem_maximalIdeal hV (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ),
    fun n x hx => ?_⟩
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨w, rfl⟩ := hx
  rw [map_mul, map_mul, norm_mul, map_pow, map_pow, norm_pow]
  have hw : ‖κ (algebraMap V (FractionRing V) w)‖ ≤ 1 := (hV _).2 ⟨w, rfl⟩
  exact mul_le_of_le_one_right (by positivity) hw
end GlobalTheory.PadicUnitBall
