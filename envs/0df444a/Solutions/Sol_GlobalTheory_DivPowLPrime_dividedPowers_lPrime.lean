-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.dividedPowers_lPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:12.835003+00:00
-- url     : https://prove2.me/submissions/5597207d-6a1f-4895-8904-2d2e7959b878

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
import Theorems.Thm_GlobalTheory_DivPowLPrime_lPrime_eq_pow
import Theorems.Thm_GlobalTheory_DivPowLPrime_one_le_lPrimeExp
import Theorems.Thm_GlobalTheory_DivPowLPrime_factorial_mul_qCoef
import Theorems.Thm_GlobalTheory_DivPowLPrime_qCoef_eq_mul
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
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime
namespace GlobalTheory.DivPowLPrime
theorem _root_.solution : ∀ (l : ℕ), l.Prime → (∀ m : ℕ, (1 ≤ m → lPrimeExp l + padicValNat l m.factorial ≤ lPrimeExp l * m) ∧ m + 2 * padicValNat l m.factorial ≤ 2 * (lPrimeExp l * m)) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (R : Type) [CommRing R] [Algebra O R], (∀ (k : ℕ) (x : R), k ≠ 0 → (k : R) * x = 0 → x = 0) → ∀ γ₀ : DividedPowers (Ideal.span {(l : R)}), (∀ (m : ℕ), ∀ y ∈ Ideal.span {(l : R)}, (m.factorial : R) * γ₀.dpow m y = y ^ m) → ∃ γ : DividedPowers (Ideal.span {(lPrime l : R)}), (∀ m : ℕ, ∃ q : O, (m.factorial : O) * q = (lPrime l : O) ^ m ∧ ∀ x : R, γ.dpow m ((lPrime l : R) * x) = algebraMap O R q * x ^ m) ∧ (∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y) ∧ ∀ n : ℕ, 1 ≤ n → γ.IsSubDPIdeal (Ideal.span {(lPrime l : R) ^ n}) ∧ ∀ (r : ℕ) (m : Fin r → ℕ) (x : Fin r → R), (∀ i, x i ∈ Ideal.span {(lPrime l : R)}) → 2 * n * lPrimeExp l ≤ ∑ i, m i → ∏ i, γ.dpow (m i) (x i) ∈ Ideal.span {(lPrime l : R) ^ n} := by
  intro l hl hnum O _ _ _ _ hlO R _ _ htf γ₀ hγ₀
  have hv : ∀ m : ℕ, padicValNat l m.factorial ≤ lPrimeExp l * m := fun m => by
    have := (hnum m).2; generalize lPrimeExp l * m = a at *; omega
  have hq : ∀ m : ℕ, (m.factorial : O) * qCoef O l m = (lPrime l : O) ^ m := fun m =>
    factorial_mul_qCoef hl hlO m (hv m)
  have hqe : ∀ m : ℕ, 1 ≤ m → lPrimeExp l ≤ qExp l m := fun m hm => by
    have := (hnum m).1 hm; unfold qExp; generalize lPrimeExp l * m = a at *; omega
  have hle : Ideal.span {(lPrime l : R)} ≤ Ideal.span {(l : R)} := by
    refine Ideal.span_singleton_le_span_singleton.2 ⟨(l : R) ^ (lPrimeExp l - 1), ?_⟩
    rw [lPrime_eq_pow, Nat.cast_pow, ← pow_succ', Nat.sub_add_cancel (one_le_lPrimeExp l)]
  have hform0 : ∀ (m : ℕ) (x : R), γ₀.dpow m ((lPrime l : R) * x) = algebraMap O R (qCoef O l m) * x ^ m := by
    intro m x
    have hmem : (lPrime l : R) * x ∈ Ideal.span {(l : R)} :=
      hle (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    apply sub_eq_zero.1
    apply htf m.factorial _ (Nat.factorial_ne_zero m)
    rw [mul_sub, hγ₀ m _ hmem, ← mul_assoc, ← map_natCast (algebraMap O R) m.factorial, ← map_mul, hq m, map_pow,
      map_natCast, mul_pow, sub_self]
  have hsub : γ₀.IsSubDPIdeal (Ideal.span {(lPrime l : R)}) :=
    { isSubideal := hle
      dpow_mem := fun n hn j hj => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hj
        rw [mul_comm, hform0, qCoef_eq_mul (hqe n (by omega)), map_mul, map_natCast, mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _) }
  let γ := DividedPowers.IsSubDPIdeal.dividedPowers γ₀ hsub
  have hγeq : ∀ (m : ℕ), ∀ y ∈ Ideal.span {(lPrime l : R)}, γ.dpow m y = γ₀.dpow m y := fun m y hy =>
    DividedPowers.IsSubDPIdeal.dpow_eq_of_mem γ₀ hsub hy
  have hform : ∀ (m : ℕ) (x : R), γ.dpow m ((lPrime l : R) * x) = algebraMap O R (qCoef O l m) * x ^ m := by
    intro m x
    rw [hγeq m _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)), hform0]
  refine ⟨γ, fun m => ⟨qCoef O l m, hq m, hform m⟩, hγeq, fun n hn => ⟨?_, ?_⟩⟩
  · exact
    { isSubideal := Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (by omega))
      dpow_mem := fun m hm j hj => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hj
        have hy : y * (lPrime l : R) ^ n = (lPrime l : R) * (y * (lPrime l : R) ^ (n - 1)) := by
          rw [mul_left_comm, ← pow_succ', Nat.sub_add_cancel hn]
        rw [hy, hform, qCoef_eq_mul (hqe m (by omega)), map_mul, map_natCast, mul_pow]
        apply Ideal.mem_span_singleton.2
        have h1 : n - 1 ≤ (n - 1) * m := Nat.le_mul_of_pos_right _ (by omega)
        have hd : (lPrime l : R) ^ n ∣ (lPrime l : R) * ((lPrime l : R) ^ (n - 1)) ^ m := by
          rw [← pow_mul, ← pow_succ']
          exact pow_dvd_pow _ (by omega)
        exact hd.trans (Dvd.intro (algebraMap O R ((l : O) ^ (qExp l m - lPrimeExp l) *
          Ring.inverse (factPrimePart l m : O)) * y ^ m) (by ring)) }
  · intro r m x hx hsum
    choose y hy using fun i => Ideal.mem_span_singleton'.1 (hx i)
    have hp : ∏ i, γ.dpow (m i) (x i) = algebraMap O R (∏ i, qCoef O l (m i)) * ∏ i, y i ^ m i := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hy i, mul_comm, hform]
    have hprod : ∏ i, qCoef O l (m i) =
        (l : O) ^ (∑ i, qExp l (m i)) * ∏ i, Ring.inverse (factPrimePart l (m i) : O) := by
      simp only [qCoef, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have h2 : ∀ i, m i ≤ 2 * qExp l (m i) := fun i => by
      have := (hnum (m i)).2; unfold qExp; generalize lPrimeExp l * m i = a at *; omega
    have h3 : ∑ i, m i ≤ 2 * ∑ i, qExp l (m i) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => h2 i
    have hN : lPrimeExp l * n ≤ ∑ i, qExp l (m i) := by nlinarith
    rw [hp, Ideal.mem_span_singleton, hprod, map_mul, map_pow, map_natCast, lPrime_eq_pow, Nat.cast_pow, ← pow_mul]
    exact ((pow_dvd_pow _ hN).mul_right _).mul_right _
end GlobalTheory.DivPowLPrime
