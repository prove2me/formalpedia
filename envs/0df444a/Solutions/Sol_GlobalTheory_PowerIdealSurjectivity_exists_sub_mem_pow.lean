-- Prove2me | solution 1 for GlobalTheory.PowerIdealSurjectivity.exists_sub_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:27.314694+00:00
-- url     : https://prove2.me/submissions/d11c3b9d-a54f-40a6-8f03-61d179fc543e

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanSubMemSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerIdealSurjectivity
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
namespace GlobalTheory.PowerIdealSurjectivity
theorem _root_.solution (B : Subalgebra O A) (I : Ideal A)
    (h0 : ∀ a, ∃ b ∈ B, a - b ∈ I) (h1 : ∀ c ∈ I, ∃ m ∈ B, m ∈ I ∧ c - m ∈ I ^ 2) (n : ℕ) (a : A) :
    ∃ b ∈ B, a - b ∈ I ^ (n + 1) := by

  have step : ∀ k : ℕ, ∀ c ∈ I ^ (k + 1), ∃ m ∈ B, m ∈ I ^ (k + 1) ∧ c - m ∈ I ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      intro c hc
      rw [zero_add, pow_one] at hc
      obtain ⟨m, hmB, hmI, hcm⟩ := h1 c hc
      exact ⟨m, hmB, by rwa [zero_add, pow_one], hcm⟩
    | succ k ih =>
      intro c hc
      have hc' : c ∈ I ^ (k + 1) * I := by rw [← pow_succ]; exact hc
      refine Submodule.mul_induction_on
        (C := fun c => ∃ m ∈ B, m ∈ I ^ (k + 1 + 1) ∧ c - m ∈ I ^ (k + 1 + 2)) hc' ?_ ?_
      · intro y hy z hz
        obtain ⟨my, hmyB, hmyI, hy'⟩ := ih y hy
        obtain ⟨mz, hmzB, hmzI, hz'⟩ := h1 z hz
        refine ⟨my * mz, B.mul_mem hmyB hmzB, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hmyI hmzI
        · have e : y * z - my * mz = y * (z - mz) + (y - my) * mz := by ring
          rw [e]
          refine Ideal.add_mem _ ?_ ?_
          · have := Ideal.mul_mem_mul hy hz'
            rwa [← pow_add] at this
          · have := Ideal.mul_mem_mul hy' hmzI
            rwa [← pow_succ] at this
      · rintro y z ⟨my, hmyB, hmyI, hy'⟩ ⟨mz, hmzB, hmzI, hz'⟩
        refine ⟨my + mz, B.add_mem hmyB hmzB, Ideal.add_mem _ hmyI hmzI, ?_⟩
        have e : y + z - (my + mz) = (y - my) + (z - mz) := by ring
        rw [e]
        exact Ideal.add_mem _ hy' hz'
  induction n with
  | zero =>
    obtain ⟨b, hb, hab⟩ := h0 a
    exact ⟨b, hb, by rwa [zero_add, pow_one]⟩
  | succ n ih =>
    obtain ⟨b, hb, hab⟩ := ih
    obtain ⟨m, hmB, -, hm⟩ := step n (a - b) hab
    refine ⟨b + m, B.add_mem hb hmB, ?_⟩
    have e : a - (b + m) = a - b - m := by ring
    rw [e]
    exact hm
end GlobalTheory.PowerIdealSurjectivity
