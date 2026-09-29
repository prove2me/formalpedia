-- Prove2me | solution 1 for MvFormalGroup.iterate_nilMul_sub_natCast_mul_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b5398d98-90a1-5c14-8a91-4ddb0958764d

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow

set_option autoImplicit false

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "nilEval nilMul coeff_single_inl toPowerSeries coeff_single_inr constantCoeff_eq_zero"
namespace KatzFG
p2m_open "MvFormalGroup"

variable {B : Type} [CommRing B] {B' : Type} [CommRing B'] [Algebra B B']

theorem prod_pow_mem_pow {σ : Type} [Fintype σ] (I : Ideal B') (a : σ → B') (ha : ∀ i, a i ∈ I) (d : σ →₀ ℕ) :
    ∏ i, a i ^ d i ∈ I ^ (∑ i, d i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ha i) _

theorem finsupp_trichotomy {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ →₀ ℕ) :
    d = 0 ∨ (∃ j, d = Finsupp.single j 1) ∨ 2 ≤ ∑ i, d i := by
  classical
  by_cases h0 : d = 0
  · exact Or.inl h0
  right
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h; push_neg at h; exact h0 (Finsupp.ext fun i => by simpa using h i)
  by_cases h1 : d = Finsupp.single j 1
  · exact Or.inl ⟨j, h1⟩
  right

  have hsplit : ∑ i, d i = d j + ∑ i ∈ Finset.univ.erase j, d i :=
    (Finset.add_sum_erase Finset.univ (fun i => d i) (Finset.mem_univ j)).symm
  rcases Nat.lt_or_ge (d j) 2 with hlt | hge
  · have hdj : d j = 1 := by omega
    obtain ⟨j', hj'ne, hj'⟩ : ∃ j', j' ≠ j ∧ d j' ≠ 0 := by
      by_contra h; push_neg at h
      apply h1
      ext i
      by_cases hij : i = j
      · subst hij; simp [hdj]
      · rw [Finsupp.single_apply, if_neg (Ne.symm hij)]
        exact h i hij
    have : d j' ≤ ∑ i ∈ Finset.univ.erase j, d i :=
      Finset.single_le_sum (f := fun i => d i) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hj'ne, Finset.mem_univ _⟩)
    omega
  · have : 0 ≤ ∑ i ∈ Finset.univ.erase j, d i := Nat.zero_le _
    omega

theorem aeval_sub_linear_mem {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal B') (k : ℕ) (hk : 1 ≤ k)
    (a : σ → B') (ha : ∀ i, a i ∈ J ^ k) (P : MvPolynomial σ B) :
    MvPolynomial.aeval a P -
      (algebraMap B B' (P.coeff 0) + ∑ j, algebraMap B B' (P.coeff (Finsupp.single j 1)) * a j) ∈ J ^ (2 * k) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rcases finsupp_trichotomy d with rfl | ⟨j, rfl⟩ | hd
      ·
        have h1 : ∀ j : σ, (MvPolynomial.monomial (0 : σ →₀ ℕ) c).coeff (Finsupp.single j 1) = 0 := fun j => by
          rw [MvPolynomial.coeff_monomial, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero).symm]
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_zero_index, mul_one, MvPolynomial.coeff_monomial, if_pos rfl,
          Finset.sum_eq_zero (fun j _ => by rw [h1 j, map_zero, zero_mul]), add_zero, sub_self]
        exact Submodule.zero_mem _
      ·
        have h0 : (MvPolynomial.monomial (Finsupp.single j 1) c).coeff 0 = 0 := by
          rw [MvPolynomial.coeff_monomial, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]
        have h1 : ∀ j' : σ, (MvPolynomial.monomial (Finsupp.single j 1) c).coeff (Finsupp.single j' 1) =
            if j' = j then c else 0 := fun j' => by
          rw [MvPolynomial.coeff_monomial]
          by_cases h : j' = j
          · subst h; simp
          · rw [if_neg, if_neg h]
            intro hh; exact h ((Finsupp.single_left_injective one_ne_zero) hh).symm
        have hsum : ∑ j', algebraMap B B' ((MvPolynomial.monomial (Finsupp.single j 1) c).coeff (Finsupp.single j' 1)) * a j' =
            algebraMap B B' c * a j := by
          rw [Finset.sum_eq_single j]
          · rw [h1, if_pos rfl]
          · intro j' _ hne; rw [h1, if_neg hne, map_zero, zero_mul]
          · intro h; exact absurd (Finset.mem_univ j) h
        have hprod : (Finsupp.single j 1).prod (fun i k => a i ^ k) = a j := by
          rw [Finsupp.prod_single_index] <;> simp
        rw [MvPolynomial.aeval_monomial, hprod, h0, map_zero, zero_add, hsum, sub_self]
        exact Submodule.zero_mem _
      ·
        have h0 : (MvPolynomial.monomial d c).coeff 0 = 0 := by
          rw [MvPolynomial.coeff_monomial, if_neg]
          rintro rfl; simp at hd
        have h1 : ∀ j : σ, (MvPolynomial.monomial d c).coeff (Finsupp.single j 1) = 0 := fun j => by
          rw [MvPolynomial.coeff_monomial, if_neg]
          rintro rfl; simp at hd
        simp only [h0, h1, map_zero, zero_mul, Finset.sum_const_zero, add_zero, sub_zero]
        rw [MvPolynomial.aeval_monomial, Finsupp.prod_pow]
        apply Ideal.mul_mem_left
        have hmem := prod_pow_mem_pow (J ^ k) a ha d
        rw [← pow_mul] at hmem
        exact Ideal.pow_le_pow_right (by nlinarith) hmem
  | add p q hp hq =>
      have := J ^ (2 * k) |>.add_mem hp hq
      convert this using 1
      simp only [map_add, MvPolynomial.coeff_add, Finset.sum_add_distrib, add_mul]
      ring

theorem nilEval_sub_linear_mem {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥)
    (k : ℕ) (hk : 1 ≤ k) (φ : MvPowerSeries σ B) (hφ : MvPowerSeries.constantCoeff φ = 0)
    (a : σ → B') (ha : ∀ i, a i ∈ J ^ k) :
    nilEval ν φ a - ∑ j, algebraMap B B' (MvPowerSeries.coeff (Finsupp.single j 1) φ) * a j ∈ J ^ (2 * k) := by
  classical
  have main := aeval_sub_linear_mem J k hk a ha
    (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : σ => ν) φ)
  have h0 : (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : σ => ν) φ).coeff 0 = 0 := by
    rw [MvPowerSeries.coeff_trunc', if_pos (show (0 : σ →₀ ℕ) ≤ _ from fun i => Nat.zero_le _)]; exact hφ
  rw [h0, map_zero, zero_add] at main
  unfold nilEval
  rcases Nat.eq_zero_or_pos ν with hν | hν
  ·
    subst hν
    rw [zero_add, pow_one] at hJ
    have hJk : J ^ k = ⊥ := by rw [hJ, ← Ideal.zero_eq_bot, zero_pow (by omega)]
    have ha0 : ∀ j, a j = 0 := fun j => by simpa [hJk] using ha j
    simp only [ha0, mul_zero, Finset.sum_const_zero, sub_zero] at main ⊢
    exact main
  · have h1 : ∀ j, (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : σ => ν) φ).coeff (Finsupp.single j 1) =
        MvPowerSeries.coeff (Finsupp.single j 1) φ := fun j => by
      rw [MvPowerSeries.coeff_trunc', if_pos]
      intro i
      rw [Finsupp.single_apply]
      show (if j = i then 1 else 0) ≤ (Finsupp.equivFunOnFinite.symm fun _ : σ => ν) i
      rw [Finsupp.coe_equivFunOnFinite_symm]
      split_ifs <;> omega
    simp only [h1] at main
    exact main

variable {g : ℕ}

theorem nilMul_sub_add_mem (F : MvFormalGroup g B) (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥) (k : ℕ) (hk : 1 ≤ k)
    (s t : Fin g → B') (hs : ∀ i, s i ∈ J ^ k) (ht : ∀ i, t i ∈ J ^ k) (i : Fin g) :
    F.nilMul ν s t i - (s i + t i) ∈ J ^ (2 * k) := by
  classical
  have hst : ∀ x : Fin g ⊕ Fin g, Sum.elim s t x ∈ J ^ k := by rintro (j | j); exacts [hs j, ht j]
  have key := nilEval_sub_linear_mem J ν hJ k hk (F.toPowerSeries i) (F.constantCoeff_eq_zero i) (Sum.elim s t) hst
  have hlin : ∑ x : Fin g ⊕ Fin g, algebraMap B B' (MvPowerSeries.coeff (Finsupp.single x 1) (F.toPowerSeries i)) *
      Sum.elim s t x = s i + t i := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr]
    simp [apply_ite (algebraMap B B'), Finset.sum_ite_eq, ite_mul]
  rw [hlin] at key
  exact key

theorem iterate_mem_and_sub_mem (F : MvFormalGroup g B) (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥) (k : ℕ)
    (hk : 1 ≤ k) (s : Fin g → B') (hs : ∀ i, s i ∈ J ^ k) (m : ℕ) :
    (∀ i, ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i ∈ J ^ k) ∧
    (∀ i, ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i - (m : B') * s i ∈ J ^ (k + 1)) := by
  have hpow : J ^ (2 * k) ≤ J ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
  have hpow' : J ^ (k + 1) ≤ J ^ k := Ideal.pow_le_pow_right (by omega)
  induction m with
  | zero =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp
      · simp
  | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hstep : ∀ i, ((fun t : Fin g → B' => F.nilMul ν t s)^[m + 1] 0) i =
          F.nilMul ν ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) s i := fun i => by
        rw [Function.iterate_succ_apply']
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [hstep]
        have h := nilMul_sub_add_mem F J ν hJ k hk _ s ih1 hs i
        have : F.nilMul ν ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) s i =
            (F.nilMul ν ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) s i -
              (((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i + s i)) +
            (((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i + s i) := by ring
        rw [this]
        exact (J ^ k).add_mem (hpow' (hpow h)) ((J ^ k).add_mem (ih1 i) (hs i))
      · rw [hstep]
        have h := nilMul_sub_add_mem F J ν hJ k hk _ s ih1 hs i
        have : F.nilMul ν ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) s i - ((m + 1 : ℕ) : B') * s i =
            (F.nilMul ν ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) s i -
              (((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i + s i)) +
            ((((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i) - (m : B') * s i) := by push_cast; ring
        rw [this]
        exact (J ^ (k + 1)).add_mem (hpow h) (ih2 i)

end MvFormalGroup.KatzFG

open MvFormalGroup.KatzFG in
theorem solution
    {B : Type} [CommRing B] {g : ℕ} (F : MvFormalGroup g B)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥)
    (k : ℕ) (hk : 1 ≤ k) (s : Fin g → B') (hs : ∀ i, s i ∈ J ^ k) (m : ℕ) (i : Fin g) :
    ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i - (m : B') * s i ∈ J ^ (k + 1) := by
  exact (iterate_mem_and_sub_mem F J ν hJ k hk s hs m).2 i

end S_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow
end P2MW
export P2MW.S_MvFormalGroup_iterate_nilMul_sub_natCast_mul_mem_pow (solution)
