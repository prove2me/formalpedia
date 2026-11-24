-- Prove2me | solution 1 for GlobalTheory.TorsionFreeDividedPowers.exists_dividedPowers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:07.748384+00:00
-- url     : https://prove2.me/submissions/2188ca87-6504-464d-b8bb-f5c2c2692332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
import Theorems.Thm_GlobalTheory_TorsionFreeDividedPowers_ofFactorialUnits_dpow
import Theorems.Thm_GlobalTheory_TorsionFreeDividedPowers_exists_factorial_mul_eq
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.TorsionFreeDividedPowers
open DividedPowers
namespace GlobalTheory.TorsionFreeDividedPowers
theorem _root_.solution :
    ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R],
    (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) →
    ∃ γ₀ : DividedPowers (Ideal.span {(l : R)}), ∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)},
      (m.factorial : R) * γ₀.dpow m y = y ^ m := by
  intro l hl O _ _ _ _ hlm R _ _ htf
  let S := natPosSubmonoid R
  have hS : S ≤ nonZeroDivisors R := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => htf k x hk hx
  have hinj : Function.Injective (algebraMap R (Localization S)) :=
    IsLocalization.injective (Localization S) hS
  have hunit : ∀ n : ℕ, IsUnit (n.factorial : Localization S) := fun n => by
    have := IsLocalization.map_units (Localization S)
      (⟨(n.factorial : R), n.factorial, Nat.factorial_ne_zero n, rfl⟩ : S)
    simpa using this
  refine ⟨DividedPowers.ofInjective (Ideal.span {(l : R)}) (Ideal.span {(l : Localization S)})
    (algebraMap R (Localization S)) hinj (ofFactorialUnits hunit _) ?_ ?_,
    fun m y hy => DividedPowers.factorial_mul_dpow_eq_pow _ hy⟩
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
  · intro n x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have hmem : algebraMap R (Localization S) (z * l) ∈ Ideal.span {(l : Localization S)} := by
      rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    rw [ofFactorialUnits_dpow hunit _ hmem]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, fun h => absurd rfl h, by simp⟩
    · obtain ⟨q, hq⟩ := exists_factorial_mul_eq l hl hlm n hn.ne'
      refine ⟨algebraMap O R q * z ^ n * l,
        fun _ => Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [eq_comm, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (hunit n)]
      have hq' : (n.factorial : R) * algebraMap O R q = (l : R) ^ (n - 1) := by
        have := congrArg (algebraMap O R) hq
        simpa using this
      have key : (n.factorial : R) * (algebraMap O R q * z ^ n * l) = (z * l) ^ n := by
        calc (n.factorial : R) * (algebraMap O R q * z ^ n * l)
            = ((n.factorial : R) * algebraMap O R q) * l * z ^ n := by ring
          _ = (z * l) ^ n := by
            rw [hq', ← pow_succ, Nat.sub_add_cancel hn, mul_pow, mul_comm]
      have := congrArg (algebraMap R (Localization S)) key
      simpa using this.symm
end GlobalTheory.TorsionFreeDividedPowers
