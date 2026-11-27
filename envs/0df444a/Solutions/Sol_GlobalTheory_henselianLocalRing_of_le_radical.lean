-- Prove2me | solution 1 for GlobalTheory.henselianLocalRing_of_le_radical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:07.712231+00:00
-- url     : https://prove2.me/submissions/668864e7-9b09-4055-9001-ec88a266b1e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (hI : maximalIdeal B ≤ I.radical) : HenselianLocalRing B where
  is_henselian f hf a₀ h₀ h₁ := by
    have key : ∀ n : ℕ, ∃ a, a - a₀ ∈ maximalIdeal B ∧ f.eval a₀ ^ 2 ^ n ∣ f.eval a ∧
        IsUnit (f.derivative.eval a) := by
      intro n
      induction n with
      | zero => exact ⟨a₀, by simp, by simp, h₁⟩
      | succ n ih =>
        obtain ⟨a, ha, hd, u, hu⟩ := ih
        have hm : f.eval a ∈ maximalIdeal B :=
          Ideal.mem_of_dvd _ hd (Ideal.pow_mem_of_mem _ h₀ _ (by positivity))
        have hy : -(↑u⁻¹ * f.eval a) ∈ maximalIdeal B := neg_mem (Ideal.mul_mem_left _ _ hm)
        refine ⟨a + -(↑u⁻¹ * f.eval a), ?_, ?_, ?_⟩
        · rw [add_sub_right_comm]
          exact add_mem ha hy
        · obtain ⟨c, hc⟩ := f.binomExpansion a (-(↑u⁻¹ * f.eval a))
          rw [hc, ← hu, mul_neg, Units.mul_inv_cancel_left, add_neg_cancel, zero_add, pow_succ,
            pow_mul, neg_sq, mul_pow]
          exact ((pow_dvd_pow_of_dvd hd 2).mul_left _).mul_left _
        · obtain ⟨c, hc⟩ := f.derivative.evalSubFactor (a + -(↑u⁻¹ * f.eval a)) a
          by_contra hn
          have h₂ := sub_mem ((mem_maximalIdeal _).mpr hn)
            (Ideal.mul_mem_left (maximalIdeal B) c hy)
          rw [add_sub_cancel_left] at hc
          rw [← hc, sub_sub_cancel, ← hu] at h₂
          exact (mem_maximalIdeal _).mp h₂ u.isUnit
    obtain ⟨n, hn⟩ := hI h₀
    obtain ⟨a, ha, hd, hu⟩ := key n
    obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian (I := I) f hf a
      (Ideal.mem_of_dvd _ hd (Ideal.pow_mem_of_pow_mem _ hn Nat.lt_two_pow_self.le)) (hu.map _)
    refine ⟨b, hb, ?_⟩
    have hle : I ≤ maximalIdeal B :=
      (HenselianRing.jac (I := I)).trans (jacobson_eq_maximalIdeal ⊥ bot_ne_top).le
    simpa using add_mem (hle hba) ha
end GlobalTheory
