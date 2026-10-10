-- Prove2me | solution 1 for IntMul.HvdH.agarwal_cooley
-- status  : ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T13:14:00.949406+00:00
-- url     : https://prove2.me/submissions/7c8db1b4-c674-48db-ac7a-05634dcf54f5

import Mathlib

namespace AgarwalCooley

/-- `x ^ n = 1` makes `x ^ m` depend only on `m % n`. -/
theorem pow_congr_mod {M : Type*} [Monoid M] (x : M) (n m m' : ℕ) (h : x ^ n = 1)
    (hm : m % n = m' % n) : x ^ m = x ^ m' := by
  have key : ∀ k, x ^ k = x ^ (k % n) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod k n]
    rw [pow_add, pow_mul, h, one_pow, one_mul]
  rw [key m, key m', hm]

/-- If every `s i` (pairwise coprime) divides the integer `z`, so does their product. -/
theorem prod_dvd {d : ℕ} (s : Fin d → ℕ) (hcop : Pairwise fun i j => Nat.Coprime (s i) (s j))
    (z : ℤ) (h : ∀ i, (s i : ℤ) ∣ z) : ((∏ i, s i : ℕ) : ℤ) ∣ z := by
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro i _ j _ hij
    exact Nat.isCoprime_iff_coprime.2 (hcop hij)
  · intro i _; exact h i

end AgarwalCooley

open AgarwalCooley in
theorem solution (d : ℕ) (s : Fin d → ℕ) (hs : ∀ i, 1 ≤ s i)
    (hcop : Pairwise fun i j => Nat.Coprime (s i) (s j)) :
    ∃ e : (Polynomial ℤ ⧸ Ideal.span {(Polynomial.X ^ (∏ i, s i) - 1 : Polynomial ℤ)}) ≃+*
        (MvPolynomial (Fin d) ℤ ⧸
          Ideal.span (Set.range fun i => (MvPolynomial.X i ^ s i - 1 : MvPolynomial (Fin d) ℤ))),
      e (Ideal.Quotient.mk _ Polynomial.X) = Ideal.Quotient.mk _ (∏ i, MvPolynomial.X i) := by
  set S := ∏ i, s i with hS
  set I := Ideal.span {(Polynomial.X ^ S - 1 : Polynomial ℤ)} with hI
  set J := Ideal.span (Set.range fun i => (MvPolynomial.X i ^ s i - 1 : MvPolynomial (Fin d) ℤ))
    with hJ
  have hS1 : 1 ≤ S := by
    rw [hS]; exact Finset.one_le_prod' fun i _ => hs i
  have : NeZero S := ⟨by omega⟩
  have hsi_dvd : ∀ i, s i ∣ S := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  -- the generators satisfy `x ^ S = 1` and `x_i ^ s_i = 1`
  have hx : (Ideal.Quotient.mk I Polynomial.X) ^ S = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hxi : ∀ i, (Ideal.Quotient.mk J (MvPolynomial.X i)) ^ s i = 1 := by
    intro i
    rw [← map_pow, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨i, rfl⟩
  -- CRT idempotent exponents: `e i ≡ 1 (mod s i)` and `e i ≡ 0 (mod s j)` for `j ≠ i`
  let P : Fin d → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, s j
  have hPcop : ∀ i, Nat.Coprime (P i) (s i) := fun i =>
    Nat.Coprime.prod_left fun j hj => hcop (Finset.ne_of_mem_erase hj)
  let e : Fin d → ℕ := fun i => P i * (((P i : ℕ) : ZMod (s i))⁻¹).val
  have he_self : ∀ i, ((e i : ℕ) : ZMod (s i)) = 1 := by
    intro i
    have : NeZero (s i) := ⟨by have := hs i; omega⟩
    simp only [e, Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ (hPcop i)
  have he_other : ∀ i j, j ≠ i → ((e i : ℕ) : ZMod (s j)) = 0 := by
    intro i j hji
    rw [ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_right
      (Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩)) _
  have he_mod : ∀ i j, e i % s j = (if j = i then 1 else 0) % s j := by
    intro i j
    rw [← ZMod.natCast_eq_natCast_iff']
    split_ifs with h
    · subst h; rw [he_self]; simp
    · rw [he_other i j h]; simp
  -- `∑ e i ≡ 1 (mod S)`
  have hsum : (∑ i, e i) % S = 1 % S := by
    rw [← ZMod.natCast_eq_natCast_iff', ← sub_eq_zero]
    have hdvd : ((S : ℕ) : ℤ) ∣ ((∑ i, e i : ℕ) : ℤ) - 1 := by
      rw [hS]
      apply prod_dvd s hcop
      intro j
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [sub_eq_zero, Finset.sum_eq_single j]
      · exact_mod_cast he_self j
      · intro i _ hij; exact_mod_cast he_other i j (Ne.symm hij)
      · intro h; exact absurd (Finset.mem_univ j) h
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ S).2 hdvd
    push_cast at this; exact_mod_cast this
  -- `S ∣ e i * s i`
  have hes : ∀ i, (e i * s i) % S = 0 % S := by
    intro i
    rw [Nat.zero_mod]
    apply Nat.mod_eq_zero_of_dvd
    have : ((S : ℕ) : ℤ) ∣ ((e i * s i : ℕ) : ℤ) := by
      rw [hS]
      apply prod_dvd s hcop
      intro j
      by_cases hji : j = i
      · subst hji; exact_mod_cast Dvd.intro_left _ rfl
      · have := (ZMod.natCast_eq_zero_iff _ _).1 (he_other i j hji)
        exact_mod_cast Dvd.dvd.mul_right this _
    exact_mod_cast this
  -- φ : ℤ[x]/(x^S - 1) → A, x ↦ x₁ ⋯ x_d
  let φ0 : Polynomial ℤ →+* (MvPolynomial (Fin d) ℤ ⧸ J) :=
    Polynomial.eval₂RingHom (Int.castRingHom _) (Ideal.Quotient.mk J (∏ i, MvPolynomial.X i))
  have hφ0 : ∀ a ∈ I, φ0 a = 0 := by
    intro a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have : φ0 (Polynomial.X ^ S - 1) = 0 := by
      simp only [φ0, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_one, map_prod, ← Finset.prod_pow]
      rw [sub_eq_zero]
      apply Finset.prod_eq_one
      intro i _
      rw [pow_congr_mod _ (s i) S 0 (hxi i) (by rw [Nat.mod_eq_zero_of_dvd (hsi_dvd i)]; simp),
        pow_zero]
    rw [map_mul, this, mul_zero]
  let φ := Ideal.Quotient.lift I φ0 hφ0
  -- ψ : A → ℤ[x]/(x^S - 1), x_i ↦ x ^ e i
  let ψ0 : MvPolynomial (Fin d) ℤ →+* (Polynomial ℤ ⧸ I) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _) fun i => (Ideal.Quotient.mk I Polynomial.X) ^ e i
  have hψ0 : ∀ a ∈ J, ψ0 a = 0 := by
    intro a ha
    have hle : J ≤ RingHom.ker ψ0 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      simp only [ψ0, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, ← pow_mul]
      rw [sub_eq_zero, pow_congr_mod _ S _ 0 hx (hes i), pow_zero]
    exact hle ha
  let ψ := Ideal.Quotient.lift J ψ0 hψ0
  have h1 : ψ.comp φ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ, ψ, φ0, ψ0]
    · simp only [φ, ψ, φ0, ψ0, RingHom.comp_apply, Ideal.Quotient.lift_mk,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_prod, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_X, RingHom.id_apply, Finset.prod_pow_eq_pow_sum]
      rw [pow_congr_mod _ S _ 1 hx hsum, pow_one]
  have h2 : φ.comp ψ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [φ, ψ, φ0, ψ0]
    · intro i
      simp only [φ, ψ, φ0, ψ0, RingHom.comp_apply, Ideal.Quotient.lift_mk,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, map_pow, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, map_prod, RingHom.id_apply, ← Finset.prod_pow]
      rw [Finset.prod_eq_single i]
      · rw [pow_congr_mod _ (s i) _ 1 (hxi i) (by rw [he_mod]; simp), pow_one]
      · intro j _ hji
        rw [pow_congr_mod _ (s j) _ 0 (hxi j) (by rw [he_mod, if_neg hji]), pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
  refine ⟨RingEquiv.ofRingHom φ ψ h2 h1, ?_⟩
  simp [φ, φ0]
