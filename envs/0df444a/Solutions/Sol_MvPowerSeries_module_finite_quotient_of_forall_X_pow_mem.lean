-- Prove2me | solution 1 for MvPowerSeries.module_finite_quotient_of_forall_X_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d8656605-3cc8-5e06-8ec0-1c69aae9a330

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem

set_option autoImplicit false

universe u v w

open MvPowerSeries

namespace TruncFinEngine

section L0

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

omit [Finite σ] in

theorem exists_le_degree_eq (N : ℕ) (x : σ →₀ ℕ) (hx : N ≤ x.degree) :
    ∃ y : σ →₀ ℕ, y ≤ x ∧ y.degree = N := by
  classical
  induction N with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨y, hyx, hyn⟩ := ih ((Nat.le_succ n).trans hx)
    have hne : x - y ≠ 0 := by
      intro h
      have hle : x ≤ y := tsub_eq_zero_iff_le.mp h
      have : x = y := le_antisymm hle hyx
      subst this
      omega
    obtain ⟨i, hi⟩ : ∃ i, (x - y) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Finsupp.ext hcon)
    refine ⟨y + Finsupp.single i 1, ?_, by simp [hyn]⟩
    intro j
    simp only [Finsupp.coe_add, Pi.add_apply]
    have hyj : y j ≤ x j := hyx j
    have hij : (x - y) i = x i - y i := Finsupp.tsub_apply x y i
    by_cases h : i = j
    · subst h
      rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_apply, if_neg h]
      omega

omit [Finite σ] in

theorem monomial_one_mem_pow_span_X (y : σ →₀ ℕ) :
    (monomial y (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ y.degree := by
  classical
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.prod_mem_prod fun i _ => ?_
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

theorem mem_of_forall_coeff_eq_zero_of_forall_monomial_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I := by
  classical

  have hY : ∀ x : σ →₀ ℕ, ∃ y : σ →₀ ℕ, N ≤ x.degree → y ≤ x ∧ y.degree = N := by
    intro x
    by_cases hx : N ≤ x.degree
    · obtain ⟨y, hy⟩ := exists_le_degree_eq N x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose Y hY using hY
  set D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le N).toFinset.filter fun y => y.degree = N
    with hD
  have hmemD : ∀ y, y ∈ D ↔ y.degree = N := by
    intro y
    simp only [hD, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
    intro h; exact h.le

  let r : (σ →₀ ℕ) → MvPowerSeries σ R := fun y z =>
    if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0
  have hr : ∀ y z, coeff z (r y) = if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0 :=
    fun y z => rfl
  have hdecomp : q = ∑ y ∈ D, monomial y (1 : R) * r y := by
    ext x
    rw [map_sum]
    simp_rw [coeff_monomial_mul, one_mul]
    by_cases hx : N ≤ x.degree
    · obtain ⟨hYx, hYdeg⟩ := hY x hx
      rw [Finset.sum_eq_single (Y x)]
      · rw [if_pos hYx, hr, tsub_add_cancel_of_le hYx, if_pos ⟨hx, rfl⟩]
      · intro y _ hne
        split_ifs with hyx
        · rw [hr, tsub_add_cancel_of_le hyx]
          rw [if_neg]
          rintro ⟨_, h⟩
          exact hne h.symm
        · rfl
      · intro h
        exact absurd ((hmemD _).mpr hYdeg) h
    · rw [hq x (not_le.mp hx)]
      symm
      refine Finset.sum_eq_zero fun y hy => ?_
      split_ifs with hyx
      · exfalso
        have := Finsupp.degree_mono hyx
        rw [(hmemD y).mp hy] at this
        exact hx this
      · rfl
  rw [hdecomp]
  refine Ideal.sum_mem _ fun y hy => ?_
  exact Ideal.mul_mem_right _ _ (hI y ((hmemD y).mp hy))

theorem mem_pow_span_X_of_forall_coeff_eq_zero (N : ℕ) (q : MvPowerSeries σ R)
    (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) :
    q ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N :=
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N _
    (fun y hy => hy ▸ monomial_one_mem_pow_span_X (R := R) y) q hq

end L0

section Trunc

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

theorem truncTotal_map {S : Type v} [CommRing S] (f : R →+* S) (N : ℕ) (q : MvPowerSeries σ R) :
    truncTotal N (MvPowerSeries.map f q) = MvPolynomial.map f (truncTotal N q) :=
  truncFinset_map f q

theorem sub_coe_truncTotal_mem_pow_span_X (N : ℕ) (q : MvPowerSeries σ R) :
    q - ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N := by
  refine mem_pow_span_X_of_forall_coeff_eq_zero N _ fun x hx => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx, sub_self]

theorem mk_coe_truncTotal (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I) (q : MvPowerSeries σ R) :
    Ideal.Quotient.mk I ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) =
      Ideal.Quotient.mk I q := by
  rw [Ideal.Quotient.eq]
  have := hI (sub_coe_truncTotal_mem_pow_span_X N q)
  rwa [← neg_sub, Ideal.neg_mem_iff] at this

end Trunc

section Bridges

variable {σ : Type w} {R : Type u} [CommRing R]

def lowVanishing (σ : Type w) (R : Type u) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {q | ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by rw [map_zero]
  smul_mem' a q hq x hx := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : ij.2 ≤ x := hij ▸ le_add_self
    rw [hq ij.2 ((Finsupp.degree_mono hj).trans_lt hx), mul_zero]

theorem mem_lowVanishing_iff (N : ℕ) (q : MvPowerSeries σ R) :
    q ∈ lowVanishing σ R N ↔ ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0 :=
  Iff.rfl

theorem span_X_le_lowVanishing_one :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ lowVanishing σ R 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩ x hx
  have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
  subst hx0
  exact coeff_zero_X i

theorem lowVanishing_mul_le (a b : ℕ) :
    lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro r hr s hs x hx
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : ij.1.degree < a
  · rw [hr ij.1 hi, zero_mul]
  · have hdeg : x.degree = ij.1.degree + ij.2.degree := by rw [← hij, map_add]
    have hj : ij.2.degree < b := by omega
    rw [hs ij.2 hj, mul_zero]

theorem pow_span_X_le_lowVanishing (N : ℕ) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ lowVanishing σ R N := by
  induction N with
  | zero =>
    intro q _ x hx
    exact absurd hx (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowVanishing_one).trans (lowVanishing_mul_le n 1)

theorem pow_span_X_le_of_forall_monomial_mem [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N I hI q (pow_span_X_le_lowVanishing N hq)

theorem pow_span_X_le_of_forall_coeff_eq_zero_imp_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ q : MvPowerSeries σ R, (∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) → q ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  hI q (pow_span_X_le_lowVanishing N hq)

theorem mem_of_pow_span_X_le [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hN : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I :=
  hN (mem_pow_span_X_of_forall_coeff_eq_zero N q hq)

theorem pow_span_X_le_of_forall_X_pow_mem [Fintype σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ i : σ, (X i : MvPowerSeries σ R) ^ N ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ (Fintype.card σ * (N - 1) + 1) ≤ I := by
  classical
  refine pow_span_X_le_of_forall_monomial_mem _ I fun y hy => ?_

  obtain ⟨i, hi⟩ : ∃ i, N ≤ y i := by
    by_contra hcon
    push Not at hcon
    have hle : y.degree ≤ Fintype.card σ * (N - 1) := by
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, y i ≤ ∑ _i : σ, (N - 1) := Finset.sum_le_sum fun i _ => by have := hcon i; omega
        _ = Fintype.card σ * (N - 1) := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    omega
  have hsplit : y = Finsupp.single i N + (y - Finsupp.single i N) := by
    rw [add_tsub_cancel_of_le]
    intro j
    by_cases hij : i = j
    · subst hij; rwa [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply, if_neg hij]; exact Nat.zero_le _
  rw [hsplit, ← one_mul (1 : R), ← monomial_mul_monomial, ← X_pow_eq]
  exact Ideal.mul_mem_right _ _ (hI i)

end Bridges

section Finite

variable {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommRing R]

theorem finite_quotient_of_forall_X_pow_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ i : σ, (X i : MvPowerSeries σ R) ^ N ∈ I) : Module.Finite R (MvPowerSeries σ R ⧸ I) := by
  classical
  set M : ℕ := Fintype.card σ * (N - 1) + 1 with hM
  have hpow := pow_span_X_le_of_forall_X_pow_mem N I hI

  let Φ : MvPolynomial σ R →ₗ[R] MvPowerSeries σ R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ (MvPolynomial.coeToMvPowerSeries.algHom R).toLinearMap
  let Ψ : ↥(MvPolynomial.restrictTotalDegree σ R M) →ₗ[R] MvPowerSeries σ R ⧸ I := Φ ∘ₗ (Submodule.subtype _)
  haveI : Module.Finite R ↥(MvPolynomial.restrictTotalDegree σ R M) := inferInstance
  refine Module.Finite.of_surjective Ψ fun x => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨⟨truncTotal M q, ?_⟩, ?_⟩
  · rw [MvPolynomial.mem_restrictTotalDegree]
    exact (totalDegree_truncTotal_lt q (by omega)).le
  · show (Ideal.Quotient.mk I) ((truncTotal M q : MvPolynomial σ R) : MvPowerSeries σ R) = Ideal.Quotient.mk I q
    exact mk_coe_truncTotal M I hpow q

end Finite

end TruncFinEngine

open TruncFinEngine in
theorem solution
    {σ : Type} [Fintype σ] {R : Type} [CommRing R] (I : Ideal (MvPowerSeries σ R)) (N : ℕ)
    (hI : ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈ I) :
    Module.Finite R (MvPowerSeries σ R ⧸ I) := by
  classical
  exact finite_quotient_of_forall_X_pow_mem N I hI

end S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem
end P2MW
export P2MW.S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem (solution)
