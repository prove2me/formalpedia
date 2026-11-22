-- Prove2me | solution 1 for MertensNumberField.exists_abs_sum_log_absNorm_div_sub_log_le
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:17:08.427033+00:00
-- url     : https://prove2.me/submissions/8dfb35b3-5aac-4af0-8f9e-5b3bd41b9e28

import Mathlib
import Theorems.Thm_TauCeti_isBigO_card_idealsLE_sub
import Theorems.Thm_TauCeti_card_filter_rationalPrimeBelow_le_finrank

open Filter Topology NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MertensNumberField_exists_abs_sum_log_absNorm_div_sub_log_le

open Finset Classical
open scoped nonZeroDivisors

/-! ### A dyadic summation lemma -/

lemma sum_rpow_le {ι : Type*} (s : Finset ι) (q w : ι → ℝ) (x C α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hC : 0 ≤ C) (hx0 : 0 ≤ x)
    (hq : ∀ i ∈ s, 1 ≤ q i ∧ q i ≤ x) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hΦ : ∀ j : ℕ, ∑ i ∈ s with 2 ^ j * q i ≤ x, w i ≤ C * (x / 2 ^ j)) :
    ∑ i ∈ s, w i * (x / q i) ^ α ≤ C * x * ((2:ℝ) ^ α / (1 - (2:ℝ) ^ α / 2)) := by
  set M : ℕ := ⌊x⌋₊ + 1
  set a : ℝ := (2:ℝ) ^ α
  have ha0 : 0 < a := Real.rpow_pos_of_pos two_pos α
  have ha2 : a < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) one_lt_two hα1
    simpa [a] using this
  -- pointwise bound
  have hpt : ∀ i ∈ s, (x / q i) ^ α ≤ ∑ j ∈ range M with 2 ^ j * q i ≤ x, a ^ (j + 1) := by
    intro i hi
    obtain ⟨hq1, hqx⟩ := hq i hi
    have hq0 : 0 < q i := by linarith
    set t := x / q i with ht
    have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hq0]; linarith
    have htx : t ≤ x := by rw [ht, div_le_iff₀ hq0]; nlinarith
    set J := Nat.log 2 ⌊t⌋₊
    have hfl : ⌊t⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊t⌋₊ := Nat.one_le_floor_iff _ |>.mpr ht1
      omega
    have h2J : ((2:ℕ) ^ J : ℝ) ≤ t := by
      have h1 : 2 ^ J ≤ ⌊t⌋₊ := Nat.pow_log_le_self 2 hfl
      calc ((2:ℕ) ^ J : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
        _ ≤ t := Nat.floor_le (by linarith)
    have ht2J : t ≤ ((2:ℕ) ^ (J + 1) : ℝ) := by
      have h1 : ⌊t⌋₊ < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h3 : (⌊t⌋₊ : ℝ) + 1 ≤ ((2 ^ (J + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h3 ⊢
      linarith
    have hJM : J ∈ (range M).filter (fun j ↦ 2 ^ j * q i ≤ x) := by
      rw [mem_filter, mem_range]
      constructor
      · have h1 : J < 2 ^ J := Nat.lt_two_pow_self
        have h2 : ((2:ℕ) ^ J : ℝ) ≤ x := le_trans h2J htx
        have h3 : 2 ^ J ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h2)
        omega
      · have : (2:ℝ) ^ J ≤ x / q i := by exact_mod_cast h2J
        rwa [le_div_iff₀ hq0] at this
    calc (x / q i) ^ α ≤ (((2:ℕ) ^ (J + 1) : ℕ) : ℝ) ^ α := by
          apply Real.rpow_le_rpow (by linarith) (by exact_mod_cast ht2J) hα0
      _ = a ^ (J + 1) := by
          push_cast
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
            Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ ∑ j ∈ range M with 2 ^ j * q i ≤ x, a ^ (j + 1) :=
          single_le_sum (f := fun j ↦ a ^ (j + 1)) (fun j _ ↦ by positivity) hJM
  -- swap the sums
  have hswap : ∑ i ∈ s, w i * (∑ j ∈ range M with 2 ^ j * q i ≤ x, a ^ (j + 1)) =
      ∑ j ∈ range M, a ^ (j + 1) * ∑ i ∈ s with 2 ^ j * q i ≤ x, w i := by
    simp_rw [sum_filter, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  calc ∑ i ∈ s, w i * (x / q i) ^ α
      ≤ ∑ i ∈ s, w i * (∑ j ∈ range M with 2 ^ j * q i ≤ x, a ^ (j + 1)) :=
        sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hpt i hi) (hw i hi)
    _ = ∑ j ∈ range M, a ^ (j + 1) * ∑ i ∈ s with 2 ^ j * q i ≤ x, w i := hswap
    _ ≤ ∑ j ∈ range M, a ^ (j + 1) * (C * (x / 2 ^ j)) :=
        sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hΦ j) (by positivity)
    _ = C * x * a * ∑ j ∈ range M, (a / 2) ^ j := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [div_pow, pow_succ]
        field_simp
    _ ≤ C * x * a * (1 - a / 2)⁻¹ := by
        have hr0 : 0 ≤ a / 2 := by positivity
        have hr1 : a / 2 < 1 := by linarith
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← tsum_geometric_of_lt_one hr0 hr1]
        exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun _ _ ↦ by positivity)
    _ = C * x * ((2:ℝ) ^ α / (1 - (2:ℝ) ^ α / 2)) := by
        rw [div_eq_mul_inv]; ring

variable (F : Type*) [Field F] [NumberField F]

lemma finite_pairs (x : ℝ) :
    {p : HeightOneSpectrum (𝓞 F) × ℕ |
      0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x}.Finite := by
  apply ((TauCeti.finite_setOf_natCast_le
    (fun v : HeightOneSpectrum (𝓞 F) ↦ Ideal.absNorm v.asIdeal) x).prod
    (Set.finite_Iic ⌊x⌋₊)).subset
  rintro ⟨v, k⟩ ⟨hk, hle⟩
  have h2 : (2:ℝ) ≤ Ideal.absNorm v.asIdeal := TauCeti.two_le_absNorm_asIdeal_real v
  refine ⟨?_, ?_⟩
  · show (Ideal.absNorm v.asIdeal : ℝ) ≤ x
    calc (Ideal.absNorm v.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
      _ ≤ x := hle
  · show k ≤ ⌊x⌋₊
    apply Nat.le_floor
    have h1 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    calc (k : ℝ) ≤ 2 ^ k := h1
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ ≤ x := hle

/-- The pairs `(v, k)` with `k ≥ 1` and `N(v)^k ≤ x`. -/
noncomputable def pairs (x : ℝ) : Finset (HeightOneSpectrum (𝓞 F) × ℕ) :=
  (finite_pairs F x).toFinset

variable {F}

lemma mem_pairs {x : ℝ} {p : HeightOneSpectrum (𝓞 F) × ℕ} :
    p ∈ pairs F x ↔ 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x :=
  Set.Finite.mem_toFinset _

lemma finsum_eq_sum_pairs (x : ℝ) (f : HeightOneSpectrum (𝓞 F) × ℕ → ℝ) :
    (∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
        (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x), f p) =
      ∑ p ∈ pairs F x, f p :=
  finsum_mem_eq_finite_toFinset_sum f (finite_pairs F x)

lemma mem_idealsLE {y : ℝ} {I : (Ideal (𝓞 F))⁰} :
    I ∈ TauCeti.idealsLE F y ↔ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ y := by
  simp [TauCeti.idealsLE, TauCeti.normLE]

lemma one_le_absNorm (I : (Ideal (𝓞 F))⁰) : 1 ≤ Ideal.absNorm (I : Ideal (𝓞 F)) := by
  have h : (I : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  have : Ideal.absNorm (I : Ideal (𝓞 F)) ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  omega

/-! ### The identity `∑_{N I ≤ x} log N I = ∑_{N v^k ≤ x} log N v · A(x / N v^k)` -/

/-- The exponent of `v` in the factorization of `J`. -/
noncomputable abbrev cnt (v : HeightOneSpectrum (𝓞 F)) (J : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk J).factors

lemma pow_dvd_iff_le_cnt (v : HeightOneSpectrum (𝓞 F)) {J : Ideal (𝓞 F)} (hJ : J ≠ 0)
    (k : ℕ) : v.asIdeal ^ k ∣ J ↔ k ≤ cnt v J := by
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  simp only [Associates.dvd_eq_le]
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible

lemma absNorm_pos {J : Ideal (𝓞 F)} (hJ : J ≠ 0) : 0 < Ideal.absNorm J := by
  have : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  omega

lemma absNorm_le_of_dvd {P J : Ideal (𝓞 F)} (hJ : J ≠ 0) (h : P ∣ J) :
    Ideal.absNorm P ≤ Ideal.absNorm J :=
  Nat.le_of_dvd (absNorm_pos hJ) (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h))

lemma pow_le_of_dvd {x : ℝ} (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) {J : Ideal (𝓞 F)}
    (hJ : J ≠ 0) (hJx : (Ideal.absNorm J : ℝ) ≤ x) (h : v.asIdeal ^ k ∣ J) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ k ≤ x := by
  have h1 := absNorm_le_of_dvd hJ h
  rw [map_pow] at h1
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ k = ((Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ Ideal.absNorm J := by exact_mod_cast h1
    _ ≤ x := hJx

lemma mem_primesLE {x : ℝ} {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ TauCeti.primesLE F x ↔ (Ideal.absNorm v.asIdeal : ℝ) ≤ x := by
  simp [TauCeti.primesLE, TauCeti.normLE]

lemma log_absNorm_eq_sum_cnt {x : ℝ} {J : Ideal (𝓞 F)} (hJ : J ≠ 0)
    (hJx : (Ideal.absNorm J : ℝ) ≤ x) :
    Real.log (Ideal.absNorm J) =
      ∑ v ∈ TauCeti.primesLE F x, (cnt v J : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) ↦ v.maxPowDividing J) ⊆
      (TauCeti.primesLE F x : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    simp only [Function.mem_mulSupport, ne_eq] at hv
    have hc : cnt v J ≠ 0 := by
      intro h0
      apply hv
      rw [HeightOneSpectrum.maxPowDividing,
        show (Associates.mk v.asIdeal).count (Associates.mk J).factors = 0 from h0, pow_zero]
    have hdvd : v.asIdeal ∣ J := (Associates.count_ne_zero_iff_dvd hJ v.irreducible).mp hc
    rw [Finset.mem_coe, mem_primesLE]
    have := pow_le_of_dvd v 1 hJ hJx (by rwa [pow_one])
    simpa using this
  have h := Ideal.finprod_heightOneSpectrum_factorization hJ
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at h
  conv_lhs => rw [← h]
  rw [map_prod, Nat.cast_prod, Real.log_prod]
  · refine sum_congr rfl fun v _ ↦ ?_
    rw [HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow, Real.log_pow]
  · intro v _
    rw [HeightOneSpectrum.maxPowDividing, map_pow, Nat.cast_pow]
    have := TauCeti.two_le_absNorm_asIdeal_real v
    exact pow_ne_zero _ (by linarith)

lemma log_absNorm_eq_sum_pairs {x : ℝ} {J : Ideal (𝓞 F)} (hJ : J ≠ 0)
    (hJx : (Ideal.absNorm J : ℝ) ≤ x) :
    Real.log (Ideal.absNorm J) =
      ∑ p ∈ pairs F x, if p.1.asIdeal ^ p.2 ∣ J then Real.log (Ideal.absNorm p.1.asIdeal)
        else 0 := by
  set B := (TauCeti.primesLE F x) ×ˢ (range (⌊x⌋₊ + 1))
  have hsubB : pairs F x ⊆ B := by
    intro p hp
    rw [mem_pairs] at hp
    have h2 : (2:ℝ) ≤ Ideal.absNorm p.1.asIdeal := TauCeti.two_le_absNorm_asIdeal_real p.1
    rw [mem_product, mem_primesLE, mem_range]
    constructor
    · calc (Ideal.absNorm p.1.asIdeal : ℝ) = (Ideal.absNorm p.1.asIdeal : ℝ) ^ 1 :=
            (pow_one _).symm
        _ ≤ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 := pow_le_pow_right₀ (by linarith) hp.1
        _ ≤ x := hp.2
    · have : p.2 ≤ ⌊x⌋₊ := by
        apply Nat.le_floor
        have h1 : (p.2 : ℝ) ≤ 2 ^ p.2 := by exact_mod_cast (Nat.lt_two_pow_self (n := p.2)).le
        calc (p.2 : ℝ) ≤ 2 ^ p.2 := h1
          _ ≤ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 := pow_le_pow_left₀ (by norm_num) h2 _
          _ ≤ x := hp.2
      omega
  have hcnt : ∀ v, cnt v J ≤ ⌊x⌋₊ := by
    intro v
    apply Nat.le_floor
    have h2 : (2:ℝ) ≤ Ideal.absNorm v.asIdeal := TauCeti.two_le_absNorm_asIdeal_real v
    have h1 : ((cnt v J : ℕ) : ℝ) ≤ 2 ^ cnt v J := by
      exact_mod_cast (Nat.lt_two_pow_self (n := cnt v J)).le
    calc ((cnt v J : ℕ) : ℝ) ≤ 2 ^ cnt v J := h1
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ cnt v J := pow_le_pow_left₀ (by norm_num) h2 _
      _ ≤ x := pow_le_of_dvd v _ hJ hJx ((pow_dvd_iff_le_cnt v hJ _).mpr le_rfl)
  -- extend the sum to `B` using the summand with the extra condition `0 < k`
  have h1 : (∑ p ∈ pairs F x, if p.1.asIdeal ^ p.2 ∣ J then Real.log (Ideal.absNorm p.1.asIdeal)
        else 0) =
      ∑ p ∈ B, if 0 < p.2 ∧ p.2 ≤ cnt p.1 J then Real.log (Ideal.absNorm p.1.asIdeal)
        else 0 := by
    rw [← sum_subset hsubB]
    · refine sum_congr rfl fun p hp ↦ ?_
      rw [mem_pairs] at hp
      simp only [pow_dvd_iff_le_cnt p.1 hJ, hp.1, true_and]
    · intro p _ hpn
      rw [if_neg]
      rintro ⟨hk, hle⟩
      apply hpn
      rw [mem_pairs]
      exact ⟨hk, pow_le_of_dvd p.1 p.2 hJ hJx ((pow_dvd_iff_le_cnt p.1 hJ _).mpr hle)⟩
  rw [h1, sum_product, log_absNorm_eq_sum_cnt hJ hJx]
  refine sum_congr rfl fun v _ ↦ ?_
  simp only [← sum_filter, sum_const, nsmul_eq_mul]
  congr 1
  have : (range (⌊x⌋₊ + 1)).filter (fun k ↦ 0 < k ∧ k ≤ cnt v J) = Icc 1 (cnt v J) := by
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    have := hcnt v
    omega
  rw [this, Nat.card_Icc]
  simp

lemma card_filter_dvd (x : ℝ) (P : Ideal (𝓞 F)) (hP : P ≠ 0) :
    ((TauCeti.idealsLE F x).filter (fun I : (Ideal (𝓞 F))⁰ ↦ P ∣ (I : Ideal (𝓞 F)))).card =
      (TauCeti.idealsLE F (x / Ideal.absNorm P)).card := by
  have hP0 : (0:ℝ) < Ideal.absNorm P := by exact_mod_cast absNorm_pos hP
  symm
  refine Finset.card_bij (fun J _ ↦ (⟨P * (J : Ideal (𝓞 F)), mem_nonZeroDivisors_of_ne_zero
    (mul_ne_zero hP (nonZeroDivisors.coe_ne_zero J))⟩ : (Ideal (𝓞 F))⁰)) ?_ ?_ ?_
  · intro J hJ
    rw [mem_filter, mem_idealsLE]
    rw [mem_idealsLE, le_div_iff₀ hP0] at hJ
    refine ⟨?_, dvd_mul_right _ _⟩
    simp only [map_mul, Nat.cast_mul]
    linarith
  · intro J1 _ J2 _ h
    apply Subtype.ext
    have h' : P * (J1 : Ideal (𝓞 F)) = P * (J2 : Ideal (𝓞 F)) := congrArg Subtype.val h
    exact mul_left_cancel₀ hP h'
  · intro I hI
    rw [mem_filter, mem_idealsLE] at hI
    obtain ⟨hIx, Q, hQ⟩ := hI
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hQ
      exact nonZeroDivisors.coe_ne_zero I hQ
    refine ⟨⟨Q, mem_nonZeroDivisors_of_ne_zero hQ0⟩, ?_, ?_⟩
    · rw [mem_idealsLE, le_div_iff₀ hP0]
      rw [hQ, map_mul, Nat.cast_mul] at hIx
      linarith
    · apply Subtype.ext
      exact hQ.symm

/-- The identity behind Mertens' theorem. -/
lemma sum_log_absNorm_eq (x : ℝ) :
    ∑ I ∈ TauCeti.idealsLE F x, Real.log (Ideal.absNorm (I : Ideal (𝓞 F))) =
      ∑ p ∈ pairs F x, Real.log (Ideal.absNorm p.1.asIdeal) *
        ((TauCeti.idealsLE F (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)).card : ℝ) := by
  rw [sum_congr rfl fun I hI ↦ log_absNorm_eq_sum_pairs (nonZeroDivisors.coe_ne_zero I)
    (mem_idealsLE.mp hI), sum_comm]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  rw [card_filter_dvd x _ (pow_ne_zero _ p.1.ne_bot), map_pow, Nat.cast_pow]

/-! ### Chebyshev's bound for `F` -/

lemma rationalPrimeBelow_prime (v : HeightOneSpectrum (𝓞 F)) :
    (TauCeti.rationalPrimeBelow v).Prime := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  exact Nat.absNorm_under_prime v.asIdeal

lemma absNorm_eq_rationalPrimeBelow_pow (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f : ℕ, Ideal.absNorm v.asIdeal = TauCeti.rationalPrimeBelow v ^ f := by
  have hp := rationalPrimeBelow_prime v
  exact ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' (p := Ideal.absNorm (Ideal.under ℤ v.asIdeal))
    v.asIdeal hp⟩

lemma rationalPrimeBelow_le (v : HeightOneSpectrum (𝓞 F)) :
    TauCeti.rationalPrimeBelow v ≤ Ideal.absNorm v.asIdeal := by
  have h1 : TauCeti.rationalPrimeBelow v ∣ Ideal.absNorm v.asIdeal :=
    Int.absNorm_under_dvd_absNorm v.asIdeal
  exact Nat.le_of_dvd (by
    have := TauCeti.two_le_absNorm_asIdeal_real v
    have : (2:ℕ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast this
    omega) h1

/-- The contribution of one prime `v` to `ψ_F(y)`. -/
lemma card_fiber_mul_log_le (y : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    (((pairs F y).filter (fun p : HeightOneSpectrum (𝓞 F) × ℕ ↦ p.1 = v)).card : ℝ) * Real.log (Ideal.absNorm v.asIdeal) ≤
      (Nat.log (TauCeti.rationalPrimeBelow v) ⌊y⌋₊ : ℝ) *
        Real.log (TauCeti.rationalPrimeBelow v) := by
  set N := Ideal.absNorm v.asIdeal with hN
  set ℓ := TauCeti.rationalPrimeBelow v
  have hN2 : 2 ≤ N := by
    have := TauCeti.two_le_absNorm_asIdeal_real v
    exact_mod_cast this
  have hℓ := rationalPrimeBelow_prime v
  set K := Nat.log N ⌊y⌋₊
  -- the fibre has at most `K` elements
  have hcard : ((pairs F y).filter (fun p : HeightOneSpectrum (𝓞 F) × ℕ ↦ p.1 = v)).card ≤ K := by
    have : ((pairs F y).filter (fun p : HeightOneSpectrum (𝓞 F) × ℕ ↦ p.1 = v)).card ≤ (Icc 1 K).card := by
      apply card_le_card_of_injOn (fun p ↦ p.2)
      · intro p hp
        simp only [coe_filter, Set.mem_setOf_eq, mem_pairs] at hp
        obtain ⟨⟨hk, hle⟩, rfl⟩ := hp
        simp only [coe_Icc, Set.mem_Icc]
        refine ⟨hk, ?_⟩
        apply Nat.le_log_of_pow_le (by omega)
        apply Nat.le_floor
        exact_mod_cast hle
      · intro p hp p' hp' h
        simp only [coe_filter, Set.mem_setOf_eq] at hp hp'
        exact Prod.ext (hp.2.trans hp'.2.symm) h
    simpa using this
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  calc (((pairs F y).filter (fun p : HeightOneSpectrum (𝓞 F) × ℕ ↦ p.1 = v)).card : ℝ) * Real.log N
      ≤ (K : ℝ) * Real.log N := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogN
    _ ≤ (Nat.log ℓ ⌊y⌋₊ : ℝ) * Real.log ℓ := by
        obtain ⟨f, hf⟩ := absNorm_eq_rationalPrimeBelow_pow v
        rw [← hN] at hf
        rcases Nat.eq_zero_or_pos K with hK | hK
        · rw [hK]; simp only [Nat.cast_zero, zero_mul]
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hℓ.one_lt.le))
        have hfl : ⌊y⌋₊ ≠ 0 := by
          intro h0; simp [K, h0] at hK
        have h1 : N ^ K ≤ ⌊y⌋₊ := Nat.pow_log_le_self N hfl
        rw [hf, ← pow_mul] at h1
        have h2 : f * K ≤ Nat.log ℓ ⌊y⌋₊ := Nat.le_log_of_pow_le hℓ.one_lt h1
        rw [hf, Nat.cast_pow, Real.log_pow, ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast hℓ.one_lt.le))
        rw [mul_comm]; exact_mod_cast h2

/-- Chebyshev's bound `ψ_F(y) ≤ [F:ℚ] (log 4 + 4) y`. -/
lemma psi_le (y : ℝ) (hy : 0 ≤ y) :
    ∑ p ∈ pairs F y, Real.log (Ideal.absNorm p.1.asIdeal) ≤
      (Module.finrank ℚ F : ℝ) * ((Real.log 4 + 4) * y) := by
  set V := (pairs F y).image Prod.fst
  set g : ℕ → ℝ := fun ℓ ↦ (Nat.log ℓ ⌊y⌋₊ : ℝ) * Real.log ℓ
  have hg0 : ∀ ℓ, 0 ≤ g ℓ := fun ℓ ↦ mul_nonneg (Nat.cast_nonneg _)
    (Real.log_natCast_nonneg ℓ)
  have step1 : ∑ p ∈ pairs F y, Real.log (Ideal.absNorm p.1.asIdeal) =
      ∑ v ∈ V, (((pairs F y).filter (fun p : HeightOneSpectrum (𝓞 F) × ℕ ↦ p.1 = v)).card : ℝ) *
        Real.log (Ideal.absNorm v.asIdeal) := by
    rw [← sum_fiberwise_of_maps_to (s := pairs F y) (t := V) (g := Prod.fst)
      (fun p hp ↦ mem_image_of_mem _ hp)]
    refine sum_congr rfl fun v _ ↦ ?_
    rw [sum_congr rfl (g := fun _ ↦ Real.log (Ideal.absNorm v.asIdeal)), sum_const, nsmul_eq_mul]
    intro p hp
    rw [(mem_filter.mp hp).2]
  have step2 : ∑ v ∈ V, (((pairs F y).filter (fun p : HeightOneSpectrum (𝓞 F) × ℕ ↦ p.1 = v)).card : ℝ) *
        Real.log (Ideal.absNorm v.asIdeal) ≤ ∑ v ∈ V, g (TauCeti.rationalPrimeBelow v) :=
    sum_le_sum fun v _ ↦ card_fiber_mul_log_le y v
  have hmaps : ∀ v ∈ V, TauCeti.rationalPrimeBelow v ∈ Nat.primesLE ⌊y⌋₊ := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    rw [mem_pairs] at hp
    have hNv : (Ideal.absNorm p.1.asIdeal : ℝ) ≤ y := by
      have h2 : (1:ℝ) ≤ Ideal.absNorm p.1.asIdeal := by
        have := TauCeti.two_le_absNorm_asIdeal_real p.1; linarith
      calc (Ideal.absNorm p.1.asIdeal : ℝ) = (Ideal.absNorm p.1.asIdeal : ℝ) ^ 1 :=
            (pow_one _).symm
        _ ≤ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 := pow_le_pow_right₀ h2 hp.1
        _ ≤ y := hp.2
    have hle : TauCeti.rationalPrimeBelow p.1 ≤ ⌊y⌋₊ :=
      (rationalPrimeBelow_le p.1).trans (Nat.le_floor hNv)
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range]
    exact ⟨by omega, rationalPrimeBelow_prime p.1⟩
  have step3 : ∑ v ∈ V, g (TauCeti.rationalPrimeBelow v) ≤
      (Module.finrank ℚ F : ℝ) * ∑ ℓ ∈ Nat.primesLE ⌊y⌋₊, g ℓ := by
    rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
    refine sum_le_sum fun ℓ _ ↦ ?_
    rw [sum_congr rfl (g := fun _ ↦ g ℓ), sum_const, nsmul_eq_mul]
    · apply mul_le_mul_of_nonneg_right _ (hg0 ℓ)
      exact_mod_cast TauCeti.card_filter_rationalPrimeBelow_le_finrank V ℓ
    · intro v hv; rw [(mem_filter.mp hv).2]
  have step4 : ∑ ℓ ∈ Nat.primesLE ⌊y⌋₊, g ℓ = Chebyshev.psi y := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_sum_mul_log_prime]
  have step5 : Chebyshev.psi y ≤ (Real.log 4 + 4) * y := Chebyshev.psi_le_const_mul_self hy
  calc _ = _ := step1
    _ ≤ _ := step2
    _ ≤ _ := step3
    _ = (Module.finrank ℚ F : ℝ) * Chebyshev.psi y := by rw [step4]
    _ ≤ _ := mul_le_mul_of_nonneg_left step5 (Nat.cast_nonneg _)

/-! ### The ideal-counting estimate in uniform form -/

lemma card_idealsLE_mono {y z : ℝ} (h : y ≤ z) :
    (TauCeti.idealsLE F y).card ≤ (TauCeti.idealsLE F z).card :=
  card_le_card fun I hI ↦ mem_idealsLE.mpr ((mem_idealsLE.mp hI).trans h)

variable (F) in
lemma exists_bound_idealCount :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ y : ℝ, 1 ≤ y →
      |((TauCeti.idealsLE F y).card : ℝ) - dedekindZeta_residue F * y| ≤
        C1 * y ^ (1 - (Module.finrank ℚ F : ℝ)⁻¹) := by
  obtain ⟨c, hc⟩ := (TauCeti.isBigO_card_idealsLE_sub F).bound
  rw [Filter.eventually_atTop] at hc
  obtain ⟨Y, hY⟩ := hc
  set Y' := max Y 1 with hY'
  set ρ := dedekindZeta_residue F
  have hρ : 0 < ρ := dedekindZeta_residue_pos F
  have hY'1 : 1 ≤ Y' := le_max_right _ _
  set α : ℝ := 1 - (Module.finrank ℚ F : ℝ)⁻¹
  have hα0 : 0 ≤ α := by
    have h1 : (1:ℝ) ≤ Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos
    have : (Module.finrank ℚ F : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    simp only [α]; linarith
  refine ⟨|c| + ((TauCeti.idealsLE F Y').card : ℝ) + ρ * Y', by positivity, fun y hy ↦ ?_⟩
  have hyα : 1 ≤ y ^ α := Real.one_le_rpow hy hα0
  have hyα0 : 0 ≤ y ^ α := by positivity
  have hAY : (0:ℝ) ≤ ((TauCeti.idealsLE F Y').card : ℝ) := Nat.cast_nonneg _
  by_cases hyY : Y ≤ y
  · have := hY y hyY
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hyα0] at this
    calc _ ≤ c * y ^ α := this
      _ ≤ |c| * y ^ α := mul_le_mul_of_nonneg_right (le_abs_self c) hyα0
      _ ≤ (|c| + ((TauCeti.idealsLE F Y').card : ℝ) + ρ * Y') * y ^ α := by
          apply mul_le_mul_of_nonneg_right _ hyα0
          nlinarith
  · push_neg at hyY
    have hA : ((TauCeti.idealsLE F y).card : ℝ) ≤ (TauCeti.idealsLE F Y').card := by
      exact_mod_cast card_idealsLE_mono (hyY.le.trans (le_max_left _ _))
    have hyY' : y ≤ Y' := hyY.le.trans (le_max_left _ _)
    have h1 : |((TauCeti.idealsLE F y).card : ℝ) - ρ * y| ≤
        ((TauCeti.idealsLE F Y').card : ℝ) + ρ * Y' := by
      rw [abs_le]
      have h0 : (0:ℝ) ≤ (TauCeti.idealsLE F y).card := Nat.cast_nonneg _
      constructor <;> nlinarith
    calc _ ≤ ((TauCeti.idealsLE F Y').card : ℝ) + ρ * Y' := h1
      _ ≤ (|c| + ((TauCeti.idealsLE F Y').card : ℝ) + ρ * Y') * 1 := by
          have := abs_nonneg c; nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hyα (by positivity)

lemma card_idealsLE_le_linear {C1 : ℝ} (hC1 : 0 ≤ C1)
    (hA : ∀ y : ℝ, 1 ≤ y →
      |((TauCeti.idealsLE F y).card : ℝ) - dedekindZeta_residue F * y| ≤
        C1 * y ^ (1 - (Module.finrank ℚ F : ℝ)⁻¹)) (y : ℝ) (hy : 0 ≤ y) :
    ((TauCeti.idealsLE F y).card : ℝ) ≤ (dedekindZeta_residue F + C1) * y := by
  have hρ : 0 < dedekindZeta_residue F := dedekindZeta_residue_pos F
  by_cases hy1 : 1 ≤ y
  · have h := hA y hy1
    have hα : y ^ (1 - (Module.finrank ℚ F : ℝ)⁻¹) ≤ y := by
      have : (0:ℝ) ≤ (Module.finrank ℚ F : ℝ)⁻¹ := by positivity
      calc y ^ (1 - (Module.finrank ℚ F : ℝ)⁻¹) ≤ y ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
        _ = y := Real.rpow_one y
    rw [abs_le] at h
    nlinarith [h.2]
  · push_neg at hy1
    have : TauCeti.idealsLE F y = ∅ := by
      apply eq_empty_of_forall_notMem
      intro I hI
      have h1 := mem_idealsLE.mp hI
      have h2 : (1:ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 F)) := by exact_mod_cast one_le_absNorm I
      linarith
    rw [this, card_empty, Nat.cast_zero]
    positivity

end Sol_MertensNumberField_exists_abs_sum_log_absNorm_div_sub_log_le

open Sol_MertensNumberField_exists_abs_sum_log_absNorm_div_sub_log_le Finset
open scoped nonZeroDivisors

theorem solution (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(∑ᶠ (p : HeightOneSpectrum (𝓞 F) × ℕ)
          (_ : 0 < p.2 ∧ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x),
          Real.log (Ideal.absNorm p.1.asIdeal : ℝ) / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) -
        Real.log x| ≤ C := by
  classical
  obtain ⟨C1, hC1, hA⟩ := exists_bound_idealCount F
  set n : ℕ := Module.finrank ℚ F with hn_def
  have hn : (1:ℝ) ≤ n := by exact_mod_cast Module.finrank_pos
  set δ : ℝ := (n:ℝ)⁻¹ with hδ_def
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hn
  set α : ℝ := 1 - δ with hα_def
  have hα0 : 0 ≤ α := by linarith
  have hα1 : α < 1 := by linarith
  set ρ := dedekindZeta_residue F with hρ_def
  have hρ : 0 < ρ := dedekindZeta_residue_pos F
  set C2 : ℝ := n * (Real.log 4 + 4) with hC2_def
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC2 : 0 ≤ C2 := by positivity
  set c : ℝ := ρ + C1 with hc_def
  have hc : 0 ≤ c := by positivity
  set Kα : ℝ := (2:ℝ) ^ α / (1 - (2:ℝ) ^ α / 2) with hKα_def
  set Kh : ℝ := (2:ℝ) ^ (1/2 : ℝ) / (1 - (2:ℝ) ^ (1/2 : ℝ) / 2) with hKh_def
  set B : ℝ := C1 * (C2 * Kα) + 2 * (c * Kh) + C1 * n with hB_def
  refine ⟨B / ρ, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  rw [finsum_eq_sum_pairs]
  set S := ∑ p ∈ pairs F x,
    Real.log (Ideal.absNorm p.1.asIdeal : ℝ) / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 with hS
  set T := ∑ I ∈ TauCeti.idealsLE F x, Real.log (Ideal.absNorm (I : Ideal (𝓞 F))) with hT_def
  -- basic facts on the pairs
  have hq : ∀ p ∈ pairs F x, 1 ≤ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ∧
      (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x := by
    intro p hp
    rw [mem_pairs] at hp
    have h2 : (2:ℝ) ≤ Ideal.absNorm p.1.asIdeal := TauCeti.two_le_absNorm_asIdeal_real p.1
    exact ⟨one_le_pow₀ (by linarith), hp.2⟩
  have hlogv : ∀ p ∈ pairs F x, 0 ≤ Real.log (Ideal.absNorm p.1.asIdeal : ℝ) := by
    intro p _
    have h2 : (2:ℝ) ≤ Ideal.absNorm p.1.asIdeal := TauCeti.two_le_absNorm_asIdeal_real p.1
    exact Real.log_nonneg (by linarith)
  -- (1) the error term `T - ρ x S`
  have hR : |T - ρ * x * S| ≤ C1 * (C2 * x * Kα) := by
    rw [hT_def, sum_log_absNorm_eq x, hS, mul_sum, ← sum_sub_distrib]
    have hpt : ∀ p ∈ pairs F x,
        |Real.log (Ideal.absNorm p.1.asIdeal) *
          ((TauCeti.idealsLE F (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)).card : ℝ) -
          ρ * x * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) /
            (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)| ≤
        C1 * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) *
          (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) ^ α) := by
      intro p hp
      obtain ⟨hq1, hqx⟩ := hq p hp
      have hq0 : 0 < (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 := by linarith
      have hy1 : 1 ≤ x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 := by
        rw [le_div_iff₀ hq0]; linarith
      have h := hA _ hy1
      have heq : Real.log (Ideal.absNorm p.1.asIdeal) *
          ((TauCeti.idealsLE F (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)).card : ℝ) -
          ρ * x * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) /
            (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) =
          Real.log (Ideal.absNorm p.1.asIdeal) *
          (((TauCeti.idealsLE F (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)).card : ℝ) -
            ρ * (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)) := by
        field_simp
      rw [heq, abs_mul, abs_of_nonneg (hlogv p hp)]
      calc _ ≤ Real.log (Ideal.absNorm p.1.asIdeal : ℝ) *
            (C1 * (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) ^ α) :=
            mul_le_mul_of_nonneg_left h (hlogv p hp)
        _ = _ := by ring
    have hΦ : ∀ j : ℕ, ∑ p ∈ pairs F x with
        2 ^ j * (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x,
        Real.log (Ideal.absNorm p.1.asIdeal : ℝ) ≤ C2 * (x / 2 ^ j) := by
      intro j
      have hsub : (pairs F x).filter
          (fun p ↦ 2 ^ j * (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2 ≤ x) ⊆ pairs F (x / 2 ^ j) := by
        intro p hp
        rw [mem_filter, mem_pairs] at hp
        rw [mem_pairs, le_div_iff₀ (by positivity)]
        exact ⟨hp.1.1, by linarith [hp.2]⟩
      calc _ ≤ ∑ p ∈ pairs F (x / 2 ^ j), Real.log (Ideal.absNorm p.1.asIdeal : ℝ) := by
            apply sum_le_sum_of_subset_of_nonneg hsub
            intro p _ _
            have h2 : (2:ℝ) ≤ Ideal.absNorm p.1.asIdeal :=
              TauCeti.two_le_absNorm_asIdeal_real p.1
            exact Real.log_nonneg (by linarith)
        _ ≤ (n : ℝ) * ((Real.log 4 + 4) * (x / 2 ^ j)) := psi_le (x / 2 ^ j) (by positivity)
        _ = C2 * (x / 2 ^ j) := by rw [hC2_def]; ring
    have hdy := sum_rpow_le (pairs F x) (fun p ↦ (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)
      (fun p ↦ Real.log (Ideal.absNorm p.1.asIdeal : ℝ)) x C2 α hα0 hα1 hC2 hx0.le hq hlogv hΦ
    calc _ ≤ ∑ p ∈ pairs F x, |Real.log (Ideal.absNorm p.1.asIdeal) *
          ((TauCeti.idealsLE F (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)).card : ℝ) -
          ρ * x * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) /
            (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ pairs F x, C1 * (Real.log (Ideal.absNorm p.1.asIdeal : ℝ) *
          (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) ^ α) := sum_le_sum hpt
      _ = C1 * ∑ p ∈ pairs F x, Real.log (Ideal.absNorm p.1.asIdeal : ℝ) *
          (x / (Ideal.absNorm p.1.asIdeal : ℝ) ^ p.2) ^ α := by rw [mul_sum]
      _ ≤ C1 * (C2 * x * Kα) := mul_le_mul_of_nonneg_left hdy hC1
  -- facts on the ideals
  have hI : ∀ I ∈ TauCeti.idealsLE F x, 1 ≤ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ∧
      (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ x := fun I hI ↦
    ⟨by exact_mod_cast one_le_absNorm I, mem_idealsLE.mp hI⟩
  -- (2) `T ≤ A(x) log x` and `A(x) log x - T = O(x)`
  have hTsub : ((TauCeti.idealsLE F x).card : ℝ) * Real.log x - T =
      ∑ I ∈ TauCeti.idealsLE F x, Real.log (x / Ideal.absNorm (I : Ideal (𝓞 F))) := by
    rw [hT_def, ← nsmul_eq_mul, ← sum_const, ← sum_sub_distrib]
    refine sum_congr rfl fun I hI' ↦ ?_
    have h1 := (hI I hI').1
    rw [Real.log_div (by linarith) (by linarith)]
  have hT1 : T ≤ ((TauCeti.idealsLE F x).card : ℝ) * Real.log x := by
    have : 0 ≤ ∑ I ∈ TauCeti.idealsLE F x, Real.log (x / Ideal.absNorm (I : Ideal (𝓞 F))) := by
      apply sum_nonneg
      intro I hI'
      obtain ⟨h1, h2⟩ := hI I hI'
      exact Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    linarith
  have hT2 : ((TauCeti.idealsLE F x).card : ℝ) * Real.log x - T ≤ 2 * (c * x * Kh) := by
    rw [hTsub]
    have hΦ : ∀ j : ℕ, ∑ I ∈ (TauCeti.idealsLE F x).filter
        (fun I : (Ideal (𝓞 F))⁰ ↦ 2 ^ j * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ x),
        (1:ℝ) ≤ c * (x / 2 ^ j) := by
      intro j
      rw [sum_const, nsmul_eq_mul, mul_one]
      have hsub : (TauCeti.idealsLE F x).filter
          (fun I : (Ideal (𝓞 F))⁰ ↦ 2 ^ j * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ x) ⊆
            TauCeti.idealsLE F (x / 2 ^ j) := by
        intro I hI'
        rw [mem_filter] at hI'
        rw [mem_idealsLE, le_div_iff₀ (by positivity)]
        linarith [hI'.2]
      calc _ ≤ ((TauCeti.idealsLE F (x / 2 ^ j)).card : ℝ) := by
            exact_mod_cast card_le_card hsub
        _ ≤ c * (x / 2 ^ j) := card_idealsLE_le_linear hC1 hA _ (by positivity)
    have hdy := sum_rpow_le (TauCeti.idealsLE F x)
      (fun I ↦ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ)) (fun _ ↦ (1:ℝ)) x c (1/2 : ℝ)
      (by norm_num) (by norm_num) hc hx0.le hI (fun _ _ ↦ zero_le_one) hΦ
    calc _ ≤ ∑ I ∈ TauCeti.idealsLE F x,
          (x / Ideal.absNorm (I : Ideal (𝓞 F))) ^ (1/2 : ℝ) / (1/2 : ℝ) := by
          apply sum_le_sum
          intro I hI'
          obtain ⟨h1, h2⟩ := hI I hI'
          exact Real.log_le_rpow_div (by positivity) (by norm_num)
      _ = 2 * ∑ I ∈ TauCeti.idealsLE F x,
          1 * (x / Ideal.absNorm (I : Ideal (𝓞 F))) ^ (1/2 : ℝ) := by
          rw [mul_sum]; refine sum_congr rfl fun I _ ↦ ?_; ring
      _ ≤ 2 * (c * x * Kh) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hdy
  -- (3) `A(x) log x = ρ x log x + O(x)`
  have hT3 : |((TauCeti.idealsLE F x).card : ℝ) * Real.log x - ρ * x * Real.log x| ≤
      C1 * n * x := by
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogle : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
    rw [← sub_mul, abs_mul, abs_of_nonneg hlog]
    have h := hA x hx
    calc _ ≤ C1 * x ^ α * Real.log x := mul_le_mul_of_nonneg_right h hlog
      _ ≤ C1 * x ^ α * (x ^ δ / δ) := mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = C1 * (x ^ α * x ^ δ) / δ := by ring
      _ = C1 * n * x := by
          rw [← Real.rpow_add hx0, hα_def, sub_add_cancel, Real.rpow_one, hδ_def]
          field_simp
  -- combine
  have key : |ρ * x * S - ρ * x * Real.log x| ≤ B * x := by
    have e : ρ * x * S - ρ * x * Real.log x =
        -(T - ρ * x * S) + (T - ((TauCeti.idealsLE F x).card : ℝ) * Real.log x) +
          (((TauCeti.idealsLE F x).card : ℝ) * Real.log x - ρ * x * Real.log x) := by ring
    rw [e]
    have h1 := abs_add_le (-(T - ρ * x * S) + (T - ((TauCeti.idealsLE F x).card : ℝ) *
      Real.log x)) (((TauCeti.idealsLE F x).card : ℝ) * Real.log x - ρ * x * Real.log x)
    have h2 := abs_add_le (-(T - ρ * x * S))
      (T - ((TauCeti.idealsLE F x).card : ℝ) * Real.log x)
    rw [abs_neg] at h2
    have h3 : |T - ((TauCeti.idealsLE F x).card : ℝ) * Real.log x| ≤ 2 * (c * x * Kh) := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      exact hT2
    have hB : B * x = C1 * (C2 * x * Kα) + 2 * (c * x * Kh) + C1 * n * x := by
      rw [hB_def]; ring
    rw [hB]
    linarith
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < ρ * x)] at key
  rw [le_div_iff₀ hρ]
  have : |S - Real.log x| * ρ * x ≤ B * x := by linarith
  exact le_of_mul_le_mul_right (by linarith) hx0
