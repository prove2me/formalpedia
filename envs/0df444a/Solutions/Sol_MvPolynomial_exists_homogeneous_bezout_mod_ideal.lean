-- Prove2me | solution 1 for MvPolynomial.exists_homogeneous_bezout_mod_ideal
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:01.961052+00:00
-- url     : https://prove2.me/submissions/62a662fc-aaa6-4755-b4fc-0bbe036c7ad0

import Mathlib

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

private theorem homogeneousComponent_mul_of_homogeneous {σ : Type} {R : Type} [CommRing R] [DecidableEq σ]
    {p : MvPolynomial σ R} {k : ℕ} (hp : p.IsHomogeneous k) (q : MvPolynomial σ R) (m : ℕ) :
    homogeneousComponent m (p * q) = if k ≤ m then p * homogeneousComponent (m - k) q else 0 := by
  classical
  ext μ
  rw [coeff_homogeneousComponent]
  have hpdeg : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → Finsupp.degree α = k := fun α hα => by
    by_contra h
    exact hα (hp.coeff_eq_zero h)
  split_ifs with hμ hk
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent]
    by_cases hα : coeff x.1 p = 0
    · rw [hα, zero_mul, zero_mul]
    · have h1 := hpdeg x.1 hα
      have h2 : Finsupp.degree x.2 = m - k := by
        have := congrArg Finsupp.degree hx
        rw [map_add, h1, hμ] at this
        omega
      rw [if_pos h2]
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hα : coeff x.1 p = 0
    · rw [hα, zero_mul]
    · exfalso
      have h1 := hpdeg x.1 hα
      have := congrArg Finsupp.degree hx
      rw [map_add, h1, hμ] at this
      omega
  · rw [coeff_mul]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent]
    split_ifs with h2
    · by_cases hα : coeff x.1 p = 0
      · rw [hα, zero_mul]
      · exfalso
        have h1 := hpdeg x.1 hα
        have := congrArg Finsupp.degree hx
        rw [map_add, h1, h2] at this
        omega
    · rw [mul_zero]
  · rw [coeff_zero]

/-- A homogeneous ideal whose intersection with a coordinate subspace is the origin
admits homogeneous Bézout certificates for a common power of every coordinate. -/
theorem _root_.solution
    {K : Type} [Field K] {S T : Type} [Fintype S] [Fintype T]
    (I : Ideal (MvPolynomial S K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule S K))
    (inc : T → S)
    (hzero : ∀ z : S → AlgebraicClosure K,
      z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
        (I ⊔ Ideal.span (Set.range
          (fun i : T => (MvPolynomial.X (inc i) : MvPolynomial S K)))) → z = 0) :
    ∃ (D : ℕ) (q : S × T → MvPolynomial S K),
      (∀ a, (q a).IsHomogeneous D) ∧
      ∀ k : S,
        MvPolynomial.X k ^ (D + 1) -
          ∑ i : T, q (k, i) * MvPolynomial.X (inc i) ∈ I := by
  classical
  let J := I ⊔ Ideal.span (Set.range
    (fun i : T => (X (inc i) : MvPolynomial S K)))
  have hrad : ∀ k : S, X k ∈ J.radical := by
    intro k
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure K) J]
    intro z hz
    simp [hzero z hz]
  have hpow : ∀ k : S, ∃ n : ℕ, X k ^ n ∈ J := by
    intro k
    exact hrad k
  choose n hn using hpow
  let D := ∑ k : S, n k
  have hbound (k : S) : n k ≤ D + 1 := by
    have h : n k ≤ D := Finset.single_le_sum (fun i _ => Nat.zero_le (n i))
      (Finset.mem_univ k)
    omega
  have huniform (k : S) : X k ^ (D + 1) ∈ J := by
    have h := J.mul_mem_left (X k ^ (D + 1 - n k)) (hn k)
    rw [← pow_add, Nat.sub_add_cancel (hbound k)] at h
    exact h
  have hexpand : ∀ p ∈ Ideal.span (Set.range
      (fun i : T => (X (inc i) : MvPolynomial S K))),
      ∃ q : T → MvPolynomial S K, ∑ i : T, q i * X (inc i) = p := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      simp
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add p r _ _ hp hr =>
      obtain ⟨q, hq⟩ := hp
      obtain ⟨s, hs⟩ := hr
      refine ⟨fun i => q i + s i, ?_⟩
      simp only [add_mul, Finset.sum_add_distrib, hq, hs]
    | smul a p _ hp =>
      obtain ⟨q, hq⟩ := hp
      refine ⟨fun i => a * q i, ?_⟩
      simp only [smul_eq_mul, mul_assoc, ← Finset.mul_sum, hq]
  have hcoeff : ∀ k : S, ∃ q : T → MvPolynomial S K,
      X k ^ (D + 1) - ∑ i : T, q i * X (inc i) ∈ I := by
    intro k
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (huniform k)
    obtain ⟨q, hq⟩ := hexpand b hb
    refine ⟨q, ?_⟩
    rw [hq, ← hab, add_sub_cancel_right]
    exact ha
  choose q hq using hcoeff
  refine ⟨D, fun a => homogeneousComponent D (q a.1 a.2),
    fun _ => homogeneousComponent_isHomogeneous _ _, ?_⟩
  intro k
  have h := homogeneousComponent_mem_of_mem hI (hq k) (D + 1)
  rw [map_sub, map_sum, homogeneousComponent_eq_self (isHomogeneous_X_pow k (D + 1))] at h
  have hmul (i : T) :
      homogeneousComponent (D + 1) (q k i * X (inc i)) =
        homogeneousComponent D (q k i) * X (inc i) := by
    rw [mul_comm (q k i),
      homogeneousComponent_mul_of_homogeneous (isHomogeneous_X K (inc i))]
    simp [mul_comm]
  simpa only [hmul] using h

end MvPolynomial
