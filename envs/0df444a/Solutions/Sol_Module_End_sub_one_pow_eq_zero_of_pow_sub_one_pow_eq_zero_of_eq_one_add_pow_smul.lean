-- Prove2me | solution 1 for Module.End.sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0ad414dd-46d4-5f04-be20-9cbab9e8ae46

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul

set_option autoImplicit false

namespace SerreMinkowskiRigidity

open Finset

section Core

variable {S : Type*} [CommRing S]

theorem eq_zero_of_eq_mul (l : S)
    (hsep : ∀ x : S, (∀ k : ℕ, ∃ z : S, l ^ k * z = x) → x = 0)
    {X Z : S} (h : X = X * (l * Z)) : X = 0 := by
  have hk : ∀ k : ℕ, X = X * (l * Z) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc X = X * (l * Z) := h
          _ = X * (l * Z) ^ k * (l * Z) := by rw [← ih]
          _ = X * (l * Z) ^ (k + 1) := by rw [pow_succ, mul_assoc]
  apply hsep
  intro k
  refine ⟨X * Z ^ k, ?_⟩
  calc l ^ k * (X * Z ^ k) = X * (l * Z) ^ k := by ring
    _ = X := (hk k).symm

theorem eq_zero_of_pow_mul_eq_zero (l : S) (htf : ∀ x : S, l * x = 0 → x = 0)
    (N : ℕ) {X : S} (h : l ^ N * X = 0) : X = 0 := by
  induction N generalizing X with
  | zero => simpa using h
  | succ N ih =>
      apply ih
      apply htf
      calc l * (l ^ N * X) = l ^ (N + 1) * X := by ring
        _ = 0 := h

theorem exists_add_mul_pow (p u T : S) (N : ℕ) : ∃ T' : S, (p + u * T) ^ N = p ^ N + u * T' := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
      obtain ⟨T', hT'⟩ := ih
      exact ⟨T' * p + p ^ N * T + u * T' * T, by rw [pow_succ, hT']; ring⟩

theorem exists_geom_sum_one_add_eq (u : S) (r : ℕ) :
    ∃ t : S, ∑ i ∈ range r, (1 + u) ^ i = (r : S) + u * t := by
  induction r with
  | zero => exact ⟨0, by simp⟩
  | succ r ih =>
      obtain ⟨t, ht⟩ := ih

      have h1 : (1 + u) ^ r = 1 + u * ∑ j ∈ range r, (1 + u) ^ j := by
        have := mul_geom_sum (1 + u) r
        rw [add_sub_cancel_left] at this
        rw [this]; ring
      refine ⟨t + ∑ j ∈ range r, (1 + u) ^ j, ?_⟩
      rw [sum_range_succ, h1, ht]
      push_cast
      ring

theorem exists_one_add_pow_sub_one_eq (u : S) (r : ℕ) :
    ∃ t : S, (1 + u) ^ r - 1 = u * ((r : S) + u * t) := by
  obtain ⟨t, ht⟩ := exists_geom_sum_one_add_eq u r
  refine ⟨t, ?_⟩
  have := mul_geom_sum (1 + u) r
  rw [add_sub_cancel_left, ht] at this
  exact this.symm

theorem pow_eq_zero_of_unit_step (l : S)
    (hsep : ∀ x : S, (∀ k : ℕ, ∃ z : S, l ^ k * z = x) → x = 0)
    (y : S) (b : ℕ) (r : ℕ) (hr : IsUnit (r : S)) (N : ℕ)
    (hN : ((1 + l ^ (b + 1) * y) ^ r - 1) ^ N = 0) : (l ^ (b + 1) * y) ^ N = 0 := by
  set u := l ^ (b + 1) * y with hu
  obtain ⟨t, ht⟩ := exists_one_add_pow_sub_one_eq u r
  rw [ht, mul_pow] at hN
  obtain ⟨T', hT'⟩ := exists_add_mul_pow (r : S) u t N
  rw [hT'] at hN

  obtain ⟨w, hw⟩ := (hr.pow N).exists_right_inv
  have key : u ^ N = u ^ N * (l * (-(l ^ b * y * T' * w))) := by
    have h1 : u ^ N * (r : S) ^ N = -(u ^ N * u * T') := by
      have : u ^ N * (r : S) ^ N + u ^ N * u * T' = 0 := by
        rw [← hN]; ring
      exact eq_neg_of_add_eq_zero_left this
    calc u ^ N = u ^ N * ((r : S) ^ N * w) := by rw [hw, mul_one]
      _ = (u ^ N * (r : S) ^ N) * w := by ring
      _ = -(u ^ N * u * T') * w := by rw [h1]
      _ = u ^ N * (l * (-(l ^ b * y * T' * w))) := by rw [hu]; ring
  exact eq_zero_of_eq_mul l hsep key

theorem exists_one_add_pow_prime_sub_one_eq (ℓ : ℕ) (hℓ : ℓ.Prime) (b : ℕ) (hb : 3 ≤ ℓ ^ (b + 1))
    (y : S) :
    ∃ v : S, (1 + (ℓ : S) ^ (b + 1) * y) ^ ℓ - 1 =
      (ℓ : S) * ((ℓ : S) ^ (b + 1) * y) * (1 + (ℓ : S) * v) := by
  set l : S := (ℓ : S) with hl
  set u := l ^ (b + 1) * y with hu
  obtain ⟨d, hd⟩ : ∃ d, ℓ = d + 2 := ⟨ℓ - 2, (Nat.sub_add_cancel hℓ.two_le).symm⟩

  have hbin : (1 + u) ^ ℓ - 1 = l * u + ∑ k ∈ range (d + 1), u ^ (k + 2) * (ℓ.choose (k + 2) : S) := by
    rw [add_comm (1 : S) u, add_pow, hd]
    rw [sum_range_succ', sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, zero_add,
      pow_one, Nat.choose_one_right]
    rw [← hd]
    rw [hl]
    ring

  have hdiv : ∀ k ∈ range (d + 1), l ^ (b + 3) * y ∣ u ^ (k + 2) * (ℓ.choose (k + 2) : S) := by
    intro k hk
    rw [mem_range] at hk
    rcases Nat.lt_or_ge (k + 2) ℓ with hlt | hge
    ·
      obtain ⟨c, hc⟩ := hℓ.dvd_choose_self (k := k + 2) (by omega) hlt
      rw [hc]
      push_cast
      rw [← hl, hu]

      have hk2 : (l ^ (b + 1) * y) ^ (k + 2) * (l * (c : S)) =
          l ^ (b + 3) * y * (l ^ ((b + 1) * (k + 2) + 1 - (b + 3)) * y ^ (k + 1) * (c : S)) := by
        have hexp : (b + 1) * (k + 2) + 1 = (b + 3) + ((b + 1) * (k + 2) + 1 - (b + 3)) := by
          have : b + 3 ≤ (b + 1) * (k + 2) + 1 := by nlinarith
          omega
        calc (l ^ (b + 1) * y) ^ (k + 2) * (l * (c : S))
            = l ^ ((b + 1) * (k + 2) + 1) * y ^ (k + 2) * (c : S) := by ring
          _ = l ^ ((b + 3) + ((b + 1) * (k + 2) + 1 - (b + 3))) * y ^ (k + 2) * (c : S) := by
              rw [← hexp]
          _ = l ^ (b + 3) * y * (l ^ ((b + 1) * (k + 2) + 1 - (b + 3)) * y ^ (k + 1) * (c : S)) := by
              ring
      rw [hk2]
      exact Dvd.intro _ rfl
    ·
      have hkeq : k + 2 = ℓ := by omega
      have hexp0 : b + 3 ≤ (b + 1) * (k + 2) := by

        rcases Nat.eq_zero_or_pos b with hb0 | hbpos
        · subst hb0
          have hk0 : k ≠ 0 := by
            rintro rfl
            rw [← hkeq] at hb
            norm_num at hb
          have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
          nlinarith
        · nlinarith
      have hexp : (b + 1) * (k + 2) = (b + 3) + ((b + 1) * (k + 2) - (b + 3)) := by omega
      have hk2 : u ^ (k + 2) * (ℓ.choose (k + 2) : S) =
          l ^ (b + 3) * y * (l ^ ((b + 1) * (k + 2) - (b + 3)) * y ^ (k + 1) * (ℓ.choose (k + 2) : S)) := by
        rw [hu]
        calc (l ^ (b + 1) * y) ^ (k + 2) * (ℓ.choose (k + 2) : S)
            = l ^ ((b + 1) * (k + 2)) * y ^ (k + 2) * (ℓ.choose (k + 2) : S) := by ring
          _ = l ^ ((b + 3) + ((b + 1) * (k + 2) - (b + 3))) * y ^ (k + 2) * (ℓ.choose (k + 2) : S) := by
              rw [← hexp]
          _ = l ^ (b + 3) * y *
                (l ^ ((b + 1) * (k + 2) - (b + 3)) * y ^ (k + 1) * (ℓ.choose (k + 2) : S)) := by ring
      rw [hk2]
      exact Dvd.intro _ rfl
  obtain ⟨v, hv⟩ := Finset.dvd_sum hdiv
  refine ⟨v, ?_⟩
  rw [hbin, hv, hu]
  ring

theorem pow_eq_zero_of_prime_step (ℓ : ℕ) (hℓ : ℓ.Prime) (b : ℕ) (hb : 3 ≤ ℓ ^ (b + 1))
    (htf : ∀ x : S, (ℓ : S) * x = 0 → x = 0)
    (hsep : ∀ x : S, (∀ k : ℕ, ∃ z : S, (ℓ : S) ^ k * z = x) → x = 0)
    (y : S) (N : ℕ)
    (hN : ((1 + (ℓ : S) ^ (b + 1) * y) ^ ℓ - 1) ^ N = 0) : ((ℓ : S) ^ (b + 1) * y) ^ N = 0 := by
  set l : S := (ℓ : S) with hl
  set u := l ^ (b + 1) * y with hu
  obtain ⟨v, hv⟩ := exists_one_add_pow_prime_sub_one_eq (S := S) ℓ hℓ b hb y
  rw [← hl, ← hu] at hv
  rw [hv] at hN

  have h1 : l ^ N * ((u * (1 + l * v)) ^ N) = 0 := by
    rw [← mul_pow, ← mul_assoc]; exact hN
  have h2 : (u * (1 + l * v)) ^ N = 0 := eq_zero_of_pow_mul_eq_zero l htf N h1
  obtain ⟨T', hT'⟩ := exists_add_mul_pow (1 : S) l v N
  rw [mul_pow, hT', one_pow] at h2
  have key : u ^ N = u ^ N * (l * (-T')) := by
    have : u ^ N + u ^ N * (l * T') = 0 := by rw [← h2]; ring
    have h3 := eq_neg_of_add_eq_zero_left this
    calc u ^ N = -(u ^ N * (l * T')) := h3
      _ = u ^ N * (l * (-T')) := by ring
  exact eq_zero_of_eq_mul l hsep key

theorem pow_eq_zero_of_pow_pow_sub_one_eq_zero (ℓ : ℕ) (hℓ : ℓ.Prime) (b : ℕ) (hb : 3 ≤ ℓ ^ (b + 1))
    (htf : ∀ x : S, (ℓ : S) * x = 0 → x = 0)
    (hsep : ∀ x : S, (∀ k : ℕ, ∃ z : S, (ℓ : S) ^ k * z = x) → x = 0)
    (N : ℕ) :
    ∀ (m : ℕ), 0 < m → (∀ r : ℕ, r.Prime → r ∣ m → r ≠ ℓ → IsUnit (r : S)) →
      ∀ y : S, ((1 + (ℓ : S) ^ (b + 1) * y) ^ m - 1) ^ N = 0 → ((ℓ : S) ^ (b + 1) * y) ^ N = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hunit y hy
    rcases Nat.lt_or_ge 1 m with h1m | hm1
    ·
      have hm1' : m ≠ 1 := by omega
      set r := m.minFac with hr
      have hrp : r.Prime := Nat.minFac_prime hm1'
      obtain ⟨m', hm'⟩ : r ∣ m := Nat.minFac_dvd m
      have hm'pos : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · rw [h0, mul_zero] at hm'; omega
        · exact h0
      have hm'lt : m' < m := by
        rw [hm']
        have : 1 < r := hrp.one_lt
        nlinarith

      set u := (ℓ : S) ^ (b + 1) * y with hu
      set y'' := y * ∑ i ∈ range m', (1 + u) ^ i with hy''
      have hpow : (1 + u) ^ m' = 1 + (ℓ : S) ^ (b + 1) * y'' := by
        have := mul_geom_sum (1 + u) m'
        rw [add_sub_cancel_left] at this
        rw [hy'', ← mul_assoc, ← hu, this]
        ring

      have hstep : ((ℓ : S) ^ (b + 1) * y'') ^ N = 0 := by
        have hy' : ((1 + (ℓ : S) ^ (b + 1) * y'') ^ r - 1) ^ N = 0 := by
          rw [← hpow, ← pow_mul, mul_comm m' r, ← hm']
          exact hy
        by_cases hrl : r = ℓ
        · rw [hrl] at hy'
          exact pow_eq_zero_of_prime_step ℓ hℓ b hb htf hsep y'' N hy'
        · exact pow_eq_zero_of_unit_step (ℓ : S) hsep y'' b r
            (hunit r hrp ⟨m', hm'⟩ hrl) N hy'

      have hy2 : ((1 + (ℓ : S) ^ (b + 1) * y) ^ m' - 1) ^ N = 0 := by
        rw [← hu, hpow, add_sub_cancel_left]
        exact hstep
      exact ih m' hm'lt hm'pos (fun r' hr' hd hne => hunit r' hr' (hd.trans ⟨r, by rw [hm', mul_comm]⟩) hne)
        y hy2
    ·
      have hm1 : m = 1 := by omega
      subst hm1
      simpa using hy

end Core

section Transfer

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem end_eq_zero_of_natCast_mul (ℓ : ℕ) (htf : ∀ x : M, (ℓ : R) • x = 0 → x = 0)
    (X : Module.End R M) (h : (ℓ : Module.End R M) * X = 0) : X = 0 := by
  ext x
  apply htf
  have := congrArg (fun F : Module.End R M => F x) h
  simpa [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul] using this

theorem end_eq_zero_of_eq_mul (ℓ : ℕ)
    (hsep : ∀ x : M, (∀ k : ℕ, ∃ z : M, (ℓ : R) ^ k • z = x) → x = 0)
    (X Z : Module.End R M) (h : X = X * ((ℓ : Module.End R M) * Z)) : X = 0 := by
  have hk : ∀ k : ℕ, X = X * ((ℓ : Module.End R M) * Z) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc X = X * ((ℓ : Module.End R M) * Z) := h
          _ = X * ((ℓ : Module.End R M) * Z) ^ k * ((ℓ : Module.End R M) * Z) := by rw [← ih]
          _ = X * ((ℓ : Module.End R M) * Z) ^ (k + 1) := by rw [pow_succ, mul_assoc]
  ext x
  simp only [LinearMap.zero_apply]
  apply hsep
  intro k
  refine ⟨X ((Z ^ k) x), ?_⟩
  have hcomm : ((ℓ : Module.End R M) * Z) ^ k = (ℓ : Module.End R M) ^ k * Z ^ k :=
    ((Nat.cast_commute ℓ Z).mul_pow k)
  conv_rhs => rw [hk k, hcomm]
  rw [Module.End.mul_apply, Module.End.mul_apply, ← Nat.cast_pow, ← Nat.cast_pow,
    Module.End.natCast_apply, Nat.cast_smul_eq_nsmul, map_nsmul]

end Transfer

end SerreMinkowskiRigidity

open SerreMinkowskiRigidity in
theorem solution
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 3 ≤ ℓ ^ a)
    (htf : ∀ x : M, (ℓ : R) • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ k : ℕ, ∃ z : M, (ℓ : R) ^ k • z = x) → x = 0)
    {m : ℕ} (hm : 0 < m) (hunit : ∀ r : ℕ, r.Prime → r ∣ m → r ≠ ℓ → IsUnit (r : R))
    (g y : Module.End R M) (hg : g = 1 + ((ℓ : R) ^ a) • y)
    {n : ℕ} (hn : (g ^ m - 1) ^ n = 0) : (g - 1) ^ n = 0 := by
  classical

  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0; norm_num at ha
    · exact ⟨a - 1, (Nat.sub_add_cancel hpos).symm⟩

  set C : Subalgebra R (Module.End R M) := Algebra.adjoin R {y} with hC
  open scoped IsMulCommutative in
  letI : CommRing C := inferInstance
  have hyC : y ∈ C := Algebra.self_mem_adjoin_singleton R y
  set y' : C := ⟨y, hyC⟩ with hy'

  have hinj : Function.Injective (fun x : C => (x : Module.End R M)) := Subtype.coe_injective
  have hnat : ∀ n : ℕ, ((n : C) : Module.End R M) = n := fun n => rfl
  have htfC : ∀ x : C, (ℓ : C) * x = 0 → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply end_eq_zero_of_natCast_mul ℓ htf
    have := congrArg (fun z : C => (z : Module.End R M)) hx
    simpa using this
  have hsepC : ∀ x : C, (∀ k : ℕ, ∃ z : C, (ℓ : C) ^ k * z = x) → x = 0 := by
    intro x hx
    apply Subtype.ext
    show (x : Module.End R M) = 0

    ext v
    simp only [LinearMap.zero_apply]
    apply hsep
    intro k
    obtain ⟨z, hz⟩ := hx k
    refine ⟨(z : Module.End R M) v, ?_⟩
    have := congrArg (fun w : C => (w : Module.End R M) v) hz
    rw [← this]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, hnat, Module.End.mul_apply]
    rw [← Nat.cast_pow, ← Nat.cast_pow, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
  have hunitC : ∀ r : ℕ, r.Prime → r ∣ m → r ≠ ℓ → IsUnit (r : C) := by
    intro r hr hd hne
    have := (hunit r hr hd hne).map (algebraMap R C)
    simpa using this

  have hcast : (ℓ : Module.End R M) ^ (b + 1) * y = ((ℓ : R) ^ (b + 1)) • y := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hgC : ((1 + (ℓ : C) ^ (b + 1) * y' : C) : Module.End R M) = g := by
    rw [hg]
    simp [hy', hcast]
  have hyp : ((1 + (ℓ : C) ^ (b + 1) * y') ^ m - 1) ^ n = 0 := by
    apply Subtype.ext
    have := hn
    rw [← hgC] at this
    simpa using this
  have hcore := pow_eq_zero_of_pow_pow_sub_one_eq_zero (S := C) ℓ hℓ b ha htfC hsepC n m hm hunitC y' hyp

  have : (((ℓ : C) ^ (b + 1) * y' : C) : Module.End R M) = g - 1 := by
    rw [hg]
    simp [hy', hcast]
  have h2 := congrArg (fun w : C => (w : Module.End R M)) hcore
  rw [← this]
  simpa using h2

end S_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
end P2MW
export P2MW.S_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul (solution)
