-- Prove2me | solution 1 for NoetherianScheme.ringOfIntegers_cyclotomic_infinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:18:37.388751+00:00
-- url     : https://prove2.me/submissions/a78146e0-5183-4f4c-9ab3-6003163c1245

import Mathlib
import Definitions.Def_NoetherianScheme_defs

universe u

open AlgebraicGeometry NumberField

theorem solution (K : Type u) [Field K] [CharZero K]
    [IsCyclotomicExtension {n : ℕ | 0 < n} ℚ K] :
    ¬ IsNoetherianRing (𝓞 K) ∧ ringKrullDim (𝓞 K) = 1 := by
  -- 2 is not a unit
  have h2 : ¬ IsUnit (2 : 𝓞 K) := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hmul : (2 : K) * (v : K) = 1 := by
      have := congrArg (algebraMap (𝓞 K) K) hv
      rw [map_mul, map_one, map_ofNat] at this
      exact this
    have hint : IsIntegral ℤ (algebraMap ℚ K (1/2)) := by
      have : algebraMap ℚ K (1/2) = (v : K) := by
        rw [map_div₀, map_one, map_ofNat]; linear_combination (-1/2 : K) * hmul
      rw [this]; exact RingOfIntegers.isIntegral_coe _
    have hq : IsIntegral ℤ ((1/2 : ℚ)) :=
      (isIntegral_algHom_iff ((Algebra.ofId ℚ K).restrictScalars ℤ)
        (algebraMap ℚ K).injective).mp hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
    have : (y : ℚ) * 2 = 1 := by
      have : algebraMap ℤ ℚ y = (y : ℚ) := rfl
      rw [← this, hy]; norm_num
    have h' : y * 2 = 1 := by exact_mod_cast this
    omega
  constructor
  · -- square roots of 2-power roots of -1
    have sqK : ∀ m : ℕ, ∀ x : K, x ^ (2 ^ m) = -1 → ∃ y : K, y ^ 2 = x ∧ y ^ (2 ^ (m+1)) = -1 := by
      intro m x hx
      obtain ⟨η, hη⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n : ℕ | 0 < n}) ℚ K
        (n := 2 ^ (m+2)) (by simp) (by positivity)
      have hη2 : IsPrimitiveRoot (η ^ 2) (2 ^ (m+1)) := hη.pow (by positivity) (by ring)
      have hx1 : x ^ (2 ^ (m+1)) = 1 := by rw [pow_succ, pow_mul, hx]; norm_num
      obtain ⟨i, -, hi⟩ := hη2.eq_pow_of_pow_eq_one hx1
      refine ⟨η ^ i, ?_, ?_⟩
      · rw [← pow_mul, mul_comm, pow_mul, hi]
      · rw [pow_succ', pow_mul, show (η ^ i) ^ 2 = x by rw [← hi, ← pow_mul, ← pow_mul, mul_comm]]
        exact hx
    have sq : ∀ m : ℕ, ∀ x : 𝓞 K, x ^ (2 ^ m) = -1 → ∃ y : 𝓞 K, y ^ 2 = x ∧ y ^ (2 ^ (m+1)) = -1 := by
      intro m x hx
      have hxK : (x : K) ^ (2 ^ m) = -1 := by
        have := congrArg (algebraMap (𝓞 K) K) hx
        simpa using this
      obtain ⟨y, hy1, hy2⟩ := sqK m x hxK
      have hyint : y ∈ integralClosure ℤ K := by
        have h1 : y ^ (2 ^ (m+2)) = 1 := by rw [pow_succ, pow_mul, hy2]; norm_num
        exact IsIntegral.of_pow (by positivity) (h1 ▸ isIntegral_one)
      let y' : 𝓞 K := ⟨y, hyint⟩
      have hy' : algebraMap (𝓞 K) K y' = y := rfl
      refine ⟨y', ?_, ?_⟩
      · apply RingOfIntegers.ext
        rw [RingOfIntegers.coe_eq_algebraMap, map_pow, hy']; exact hy1
      · apply RingOfIntegers.ext
        rw [RingOfIntegers.coe_eq_algebraMap, map_pow, hy', RingOfIntegers.coe_eq_algebraMap,
          map_neg, map_one]; exact hy2
    choose g hg1 hg2 using sq
    let w : (k : ℕ) → {x : 𝓞 K // x ^ (2 ^ k) = -1} := fun k =>
      Nat.rec ⟨-1, by simp⟩ (fun k x => ⟨g k x.1 x.2, hg2 k x.1 x.2⟩) k
    have hw0 : (w 0).1 = -1 := rfl
    have hws : ∀ k, (w (k+1)).1 ^ 2 = (w k).1 := fun k => hg1 k (w k).1 (w k).2
    have hwp : ∀ k, (w k).1 ^ (2 ^ k) = -1 := fun k => (w k).2
    set a : ℕ → 𝓞 K := fun k => 1 - (w k).1 with ha
    have hfac : ∀ k, a k = a (k+1) * (1 + (w (k+1)).1) := by
      intro k; simp only [ha]; rw [← hws k]; ring
    have hN : ∀ k, (w (k+1)).1 ^ (2 ^ (k+1) + 1) = -(w (k+1)).1 := by
      intro k; rw [pow_succ, hwp]; ring
    have dvd1 : ∀ k, a (k+1) ∣ 1 + (w (k+1)).1 := by
      intro k
      have := sub_dvd_pow_sub_pow (1 : 𝓞 K) (w (k+1)).1 (2 ^ (k+1) + 1)
      rw [one_pow, hN] at this
      simpa [ha] using this
    have dvd2 : ∀ k, 1 + (w (k+1)).1 ∣ a (k+1) := by
      intro k
      have := sub_dvd_pow_sub_pow (1 : 𝓞 K) (-(w (k+1)).1) (2 ^ (k+1) + 1)
      have hodd : Odd (2 ^ (k+1) + 1) := by
        refine Even.add_one ?_
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rw [one_pow, hodd.neg_pow, hN, neg_neg] at this
      simpa [ha, sub_neg_eq_add] using this
    have hnu : ∀ k, ¬ IsUnit (a k) := by
      intro k
      induction k with
      | zero => simp only [ha, hw0]; norm_num; exact h2
      | succ k ih =>
        intro hu
        apply ih
        rw [hfac k]
        exact hu.mul (isUnit_of_dvd_unit (dvd2 k) hu)
    have hne : ∀ k, a k ≠ 0 := by
      intro k h
      have h1 : (w k).1 = 1 := by simp only [ha] at h; linear_combination -h
      have := hwp k
      rw [h1, one_pow] at this
      have := congrArg (algebraMap (𝓞 K) K) this
      simp at this
      norm_num at this
    intro hN'
    have hmono : Monotone (fun k => (Ideal.span {a k} : Ideal (𝓞 K))) := by
      refine monotone_nat_of_le_succ fun k => ?_
      rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨_, hfac k⟩
    obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian (R := 𝓞 K) (M := 𝓞 K)).mpr hN'
      ⟨fun k => Ideal.span {a k}, hmono⟩
    have heq := hn (n+1) (by omega)
    simp only [OrderHom.coe_mk] at heq
    have hd : a n ∣ a (n+1) := by
      rw [← Ideal.span_singleton_le_span_singleton, heq]
    obtain ⟨c, hc⟩ := hd
    have h1 : a (n+1) * ((1 + (w (n+1)).1) * c) = a (n+1) * 1 := by
      rw [mul_one, ← mul_assoc, ← hfac n, ← hc]
    have hu : IsUnit (1 + (w (n+1)).1) :=
      have h3 := mul_left_cancel₀ (hne (n+1)) h1
      ⟨⟨_, c, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
    exact hnu (n+1) (isUnit_of_dvd_unit (dvd1 n) hu)
  · have hnf : ¬ IsField (𝓞 K) := fun hf => h2 (by
      obtain ⟨b, hb⟩ := hf.mul_inv_cancel (a := (2 : 𝓞 K)) two_ne_zero
      exact ⟨⟨2, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩)
    have hle : Ring.KrullDimLE 1 (𝓞 K) := by
      refine Ring.KrullDimLE.mk₁' fun I hI hp => ?_
      have : Algebra.IsIntegral ℤ (𝓞 K) := ⟨fun x => RingOfIntegers.isIntegral x⟩
      apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
      have hc : I.comap (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
        intro h
        exact hI (Ideal.eq_bot_of_comap_eq_bot h)
      have : (I.comap (algebraMap ℤ (𝓞 K))).IsPrime := Ideal.comap_isPrime _ _
      exact Ideal.IsPrime.isMaximal inferInstance hc
    apply eq_of_le_of_not_lt
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]; exact hle
    · intro h'
      have h'' : ringKrullDim (𝓞 K) ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact hnf Ring.KrullDimLE.isField_of_isDomain
