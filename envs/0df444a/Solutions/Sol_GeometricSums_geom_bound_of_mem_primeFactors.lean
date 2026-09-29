-- Prove2me | solution 1 for GeometricSums.geom_bound_of_mem_primeFactors
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:12:28.562525+00:00
-- url     : https://prove2.me/submissions/10f2f1ce-a116-4416-9392-0dc669841c4b

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Brun.M3Expansion =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# N3.2 — the ν* geometric expansion (radical grouping)

For the twin sieve `ν(2) = 1/2`, `ν(p) = 2/p` (odd `p`), the multiplicative
extension `ν*` takes the value `2^Ω(m)/m` on odd `m` (`Ω` = number of prime
factors with multiplicity).  Grouping the naturals by their radical
`rad m = ∏ p∣m p` and summing the geometric series in each prime turns the
`ν*`-sum into the Selberg product

`g(ℓ) = ∏_{p∣ℓ} 2/(p-2)`.

Truncating `m < z` and dropping the (nonnegative) tail gives the one-sided bound

`∑_{m < z, odd} ν*(m) ≤ ∑_{ℓ < z, odd sqfree} g(ℓ)`.

This file proves that bound from scratch.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Omega

namespace Salt.M3Expansion

/-- The twin `ν*` on a natural: `2^Ω(m)/m` (its value on odd `m`). -/
noncomputable def nuStar (m : ℕ) : ℝ := 2 ^ (Ω m) / (m : ℝ)

/-- The twin Selberg term on an odd squarefree `ℓ`, as a bare product. -/
noncomputable def gTwin (ℓ : ℕ) : ℝ := ∏ p ∈ ℓ.primeFactors, (2 : ℝ) / (p - 2)

/-- The radical (product of the distinct prime factors). -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- If `rad m = ℓ` then `m` and `ℓ` have the same prime factors. -/
lemma rad_eq_primeFactors {m ℓ : ℕ} (h : rad m = ℓ) : m.primeFactors = ℓ.primeFactors := by
  rw [← h, rad]
  exact (Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)).symm

/-- The radical of an odd number is odd. -/
lemma rad_odd {m : ℕ} (hm : Odd m) : Odd (rad m) := by
  have hdvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
  rw [← Nat.coprime_two_left] at hm ⊢
  exact hm.coprime_dvd_right hdvd

/-- The radical is squarefree. -/
lemma rad_squarefree (m : ℕ) : Squarefree (rad m) := by
  rw [rad]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp ha))
        (Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hb))).mpr hab)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).prime.squarefree

/-- `ν*(m) = ∏_{p∣m} (2/p)^{v_p(m)}` for `m ≠ 0`. -/
lemma nuStar_eq {m : ℕ} (hm : m ≠ 0) :
    nuStar m = ∏ p ∈ m.primeFactors, ((2 : ℝ) / (p : ℝ)) ^ (m.factorization p) := by
  have hΩ : (Ω m : ℕ) = ∑ p ∈ m.primeFactors, m.factorization p := by
    rw [cardFactors_eq_sum_factorization]
    simp only [Finsupp.sum, Nat.support_factorization]
  have hprodnat : ∏ p ∈ m.primeFactors, p ^ (m.factorization p) = m := by
    have h := Nat.prod_factorization_pow_eq_self hm
    rwa [Finsupp.prod, Nat.support_factorization] at h
  have hden : ∏ p ∈ m.primeFactors, ((p : ℝ)) ^ (m.factorization p) = (m : ℝ) := by
    have hcast : ((∏ p ∈ m.primeFactors, p ^ (m.factorization p) : ℕ) : ℝ) = (m : ℝ) := by
      rw [hprodnat]
    rw [Nat.cast_prod] at hcast
    simp only [Nat.cast_pow] at hcast
    exact hcast
  simp only [nuStar]
  rw [hΩ, ← hden, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [div_pow]

/-- Per-prime geometric bound: for an odd `ℓ` and `p ∣ ℓ` (so `p ≥ 3`),
`∑_{j=1}^{K} (2/p)^j ≤ 2/(p-2)`. -/
lemma geom_bound {ℓ p : ℕ} (hℓodd : Odd ℓ) (hp : p ∈ ℓ.primeFactors) (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, ((2 : ℝ) / (p : ℝ)) ^ j ≤ (2 : ℝ) / ((p : ℝ) - 2) := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ ℓ := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hℓodd)) hpdvd
  have hp3 : 3 ≤ p := by have := hpprime.two_le; omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set r : ℝ := (2 : ℝ) / (p : ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hp0]; linarith
  have hshift : ∀ N : ℕ, ∑ j ∈ Finset.Icc 1 N, r ^ j = r * ∑ j ∈ Finset.range N, r ^ j := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]; ring
  rw [hshift K]
  have hgeo : ∑ j ∈ Finset.range K, r ^ j ≤ (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (fun i _ => by positivity)
  calc r * ∑ j ∈ Finset.range K, r ^ j
      ≤ r * (1 - r)⁻¹ := by exact mul_le_mul_of_nonneg_left hgeo hr0
    _ = (2 : ℝ) / ((p : ℝ) - 2) := by
        rw [hr]
        have hpne : (p : ℝ) ≠ 0 := by linarith
        have hp2ne : (p : ℝ) - 2 ≠ 0 := by linarith
        have h1 : (0 : ℝ) < 1 - 2 / (p : ℝ) := by rw [sub_pos, div_lt_one hp0]; linarith
        field_simp

/-- The crux: for each odd `ℓ`, the `ν*`-mass of the radical fiber below `z`
is at most `g(ℓ)`. -/
lemma radical_fiber_bound (z ℓ : ℕ) (hℓodd : Odd ℓ) :
    ∑ m ∈ ((Finset.range z).filter Odd).filter (fun m => rad m = ℓ), nuStar m ≤ gTwin ℓ := by
  classical
  set F := ((Finset.range z).filter Odd).filter (fun m => rad m = ℓ) with hF
  -- properties of fiber elements
  have hFprop : ∀ m ∈ F, Odd m ∧ m < z ∧ rad m = ℓ := by
    intro m hm
    rw [hF, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hm
    exact ⟨hm.1.2, hm.1.1, hm.2⟩
  -- the exponent function attached to each fiber element
  let φ : ℕ → (∀ p ∈ ℓ.primeFactors, ℕ) := fun m p _ => m.factorization p
  -- value of the summand on a fiber element
  have hval : ∀ m ∈ F, nuStar m
      = ∏ x ∈ ℓ.primeFactors.attach, ((2 : ℝ) / ((x : ℕ) : ℝ)) ^ (m.factorization (x : ℕ)) := by
    intro m hm
    obtain ⟨hmodd, _, hmrad⟩ := hFprop m hm
    have hm0 : m ≠ 0 := by rintro rfl; simp at hmodd
    have hpfm : m.primeFactors = ℓ.primeFactors := rad_eq_primeFactors hmrad
    rw [nuStar_eq hm0, hpfm, ← Finset.prod_attach]
  -- injectivity of φ on the fiber
  have hinj : Set.InjOn φ ↑F := by
    intro a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    obtain ⟨hao, _, harad⟩ := hFprop a ha
    obtain ⟨hbo, _, hbrad⟩ := hFprop b hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at hao
    have hb0 : b ≠ 0 := by rintro rfl; simp at hbo
    apply Nat.eq_of_factorization_eq ha0 hb0
    intro q
    by_cases hq : q ∈ ℓ.primeFactors
    · exact congrFun (congrFun hab q) hq
    · have hqa : a.factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization, rad_eq_primeFactors harad]
        exact hq
      have hqb : b.factorization q = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization, rad_eq_primeFactors hbrad]
        exact hq
      rw [hqa, hqb]
  -- image of the fiber lands in the exponent grid
  have hsub : F.image φ ⊆ ℓ.primeFactors.pi (fun _ => Finset.Icc 1 z) := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨m, hmF, rfl⟩ := he
    obtain ⟨hmodd, hmz, hmrad⟩ := hFprop m hmF
    have hm0 : m ≠ 0 := by rintro rfl; simp at hmodd
    have hpfm : m.primeFactors = ℓ.primeFactors := rad_eq_primeFactors hmrad
    rw [Finset.mem_pi]
    intro p hp
    change m.factorization p ∈ Finset.Icc 1 z
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have hpm : p ∈ m.primeFactors := by rw [hpfm]; exact hp
      exact (Nat.prime_of_mem_primeFactors hpm).factorization_pos_of_dvd hm0
        (Nat.dvd_of_mem_primeFactors hpm)
    · have hlt : m.factorization p < m := Nat.factorization_lt p hm0
      omega
  -- assemble
  calc ∑ m ∈ F, nuStar m
      = ∑ e ∈ F.image φ,
          ∏ x ∈ ℓ.primeFactors.attach, ((2 : ℝ) / ((x : ℕ) : ℝ)) ^ (e (x : ℕ) x.2) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl (fun m hm => hval m hm)
    _ ≤ ∑ e ∈ ℓ.primeFactors.pi (fun _ => Finset.Icc 1 z),
          ∏ x ∈ ℓ.primeFactors.attach, ((2 : ℝ) / ((x : ℕ) : ℝ)) ^ (e (x : ℕ) x.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro e _ _
        exact Finset.prod_nonneg (fun x _ => by positivity)
    _ = ∏ p ∈ ℓ.primeFactors, ∑ j ∈ Finset.Icc 1 z, ((2 : ℝ) / (p : ℝ)) ^ j :=
        (Finset.prod_sum ℓ.primeFactors (fun _ => Finset.Icc 1 z)
          (fun p j => ((2 : ℝ) / (p : ℝ)) ^ j)).symm
    _ ≤ ∏ p ∈ ℓ.primeFactors, (2 : ℝ) / ((p : ℝ) - 2) := by
        apply Finset.prod_le_prod
        · intro p _
          exact Finset.sum_nonneg (fun j _ => by positivity)
        · intro p hp
          exact geom_bound hℓodd hp z
    _ = gTwin ℓ := by rw [gTwin]

/-- **N3.2**: the `ν*`-sum over odd naturals below `z` is bounded by the sum of
the twin Selberg terms `g(ℓ)` over odd squarefree `ℓ < z`. -/
theorem nuStar_sum_le_gTwin_sum (z : ℕ) :
    (∑ m ∈ (Finset.range z).filter Odd, nuStar m)
      ≤ ∑ ℓ ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ), gTwin ℓ := by
  have hmaps : ∀ m ∈ (Finset.range z).filter Odd,
      rad m ∈ (Finset.range z).filter (fun ℓ => Odd ℓ ∧ Squarefree ℓ) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmz, hmodd⟩ := hm
    have hm0 : m ≠ 0 := by rintro rfl; simp at hmodd
    have hdvd : rad m ∣ m := Nat.prod_primeFactors_dvd m
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, rad_odd hmodd, rad_squarefree m⟩
    calc rad m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
      _ < z := hmz
  rw [← Finset.sum_fiberwise_of_maps_to hmaps nuStar]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  exact radical_fiber_bound z ℓ (Finset.mem_filter.mp hℓ).2.1

end Salt.M3Expansion

end




theorem solution {ℓ p : ℕ} (hℓodd : Odd ℓ) (hp : p ∈ ℓ.primeFactors) (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, ((2 : ℝ) / (p : ℝ)) ^ j ≤ (2 : ℝ) / ((p : ℝ) - 2) := by
  apply Salt.M3Expansion.geom_bound <;> assumption

