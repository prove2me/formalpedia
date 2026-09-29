-- Prove2me | solution 1 for MvPowerSeries.exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/61cbc99d-f88d-5214-bfa7-20a262770d09

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename

set_option autoImplicit false

universe u v w x

open scoped TensorProduct
open Finsupp

noncomputable section

namespace TQ

section Curry

variable {σ τ : Type v} {R : Type u} [CommRing R]

def curryFun (f : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries σ (MvPowerSeries τ R) :=
  fun d₁ d₂ => f (d₁.sumElim d₂)

def uncurryFun (g : MvPowerSeries σ (MvPowerSeries τ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn) (d.comapDomain Sum.inr Sum.inr_injective.injOn)

theorem coeff_coeff_curryFun (f : MvPowerSeries (σ ⊕ τ) R) (d₁ : σ →₀ ℕ) (d₂ : τ →₀ ℕ) :
    MvPowerSeries.coeff d₂ (MvPowerSeries.coeff d₁ (curryFun f)) = MvPowerSeries.coeff (d₁.sumElim d₂) f := rfl

omit [CommRing R] in
theorem uncurryFun_curryFun [CommRing R] (f : MvPowerSeries (σ ⊕ τ) R) : uncurryFun (curryFun f) = f := by
  funext d
  change f (sumElim (d.comapDomain Sum.inl Sum.inl_injective.injOn) (d.comapDomain Sum.inr Sum.inr_injective.injOn)) = f d
  rw [comapDomain_sumElim_comapDomain]

theorem curryFun_uncurryFun (g : MvPowerSeries σ (MvPowerSeries τ R)) : curryFun (uncurryFun g) = g := by
  funext d₁ d₂
  change g ((d₁.sumElim d₂).comapDomain Sum.inl Sum.inl_injective.injOn) ((d₁.sumElim d₂).comapDomain Sum.inr Sum.inr_injective.injOn) = g d₁ d₂
  rw [comapDomain_inl_sumElim, comapDomain_inr_sumElim]

def curryLinearEquiv : MvPowerSeries (σ ⊕ τ) R ≃ₗ[R] MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := curryFun
  invFun := uncurryFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := uncurryFun_curryFun
  right_inv := curryFun_uncurryFun

omit [CommRing R] in
theorem sumElim_eq_zero_iff (d₁ : σ →₀ ℕ) (d₂ : τ →₀ ℕ) : d₁.sumElim d₂ = 0 ↔ d₁ = 0 ∧ d₂ = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← comapDomain_inl_sumElim d₁ d₂, h]; exact comapDomain_zero _ _
    · rw [← comapDomain_inr_sumElim d₁ d₂, h]; exact comapDomain_zero _ _
  · rintro ⟨rfl, rfl⟩
    exact sumElim_zero_zero

omit [CommRing R] in
theorem sumElim_injective2 {d₁ d₁' : σ →₀ ℕ} {d₂ d₂' : τ →₀ ℕ} (h : d₁.sumElim d₂ = d₁'.sumElim d₂') : d₁ = d₁' ∧ d₂ = d₂' := by
  constructor
  · rw [← comapDomain_inl_sumElim d₁ d₂, h, comapDomain_inl_sumElim]
  · rw [← comapDomain_inr_sumElim d₁ d₂, h, comapDomain_inr_sumElim]

theorem curryFun_one [DecidableEq σ] [DecidableEq τ] : curryFun (1 : MvPowerSeries (σ ⊕ τ) R) = 1 := by
  classical
  funext d₁ d₂
  change MvPowerSeries.coeff (d₁.sumElim d₂) (1 : MvPowerSeries (σ ⊕ τ) R) =
    MvPowerSeries.coeff d₂ (MvPowerSeries.coeff d₁ (1 : MvPowerSeries σ (MvPowerSeries τ R)))
  rw [MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
  by_cases h₁ : d₁ = 0
  · subst h₁
    rw [if_pos rfl, MvPowerSeries.coeff_one]
    by_cases h₂ : d₂ = 0
    · subst h₂; rw [if_pos sumElim_zero_zero, if_pos rfl]
    · rw [if_neg h₂, if_neg (fun h => h₂ ((sumElim_eq_zero_iff _ _).1 h).2)]
  · rw [if_neg h₁, if_neg (fun h => h₁ ((sumElim_eq_zero_iff _ _).1 h).1)]
    rfl

theorem curryFun_mul [DecidableEq σ] [DecidableEq τ] (f g : MvPowerSeries (σ ⊕ τ) R) :
    curryFun (f * g) = curryFun f * curryFun g := by
  classical
  funext d₁ d₂
  change MvPowerSeries.coeff (d₁.sumElim d₂) (f * g) = MvPowerSeries.coeff d₂ (MvPowerSeries.coeff d₁ (curryFun f * curryFun g))
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, ← image_sumElim_product_antidiagonal, Finset.sum_image]
  · have hadd : ∀ (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) (F : (σ →₀ ℕ) × (σ →₀ ℕ) → MvPowerSeries τ R),
        MvPowerSeries.coeff d₂ (∑ q ∈ s, F q) = ∑ q ∈ s, MvPowerSeries.coeff d₂ (F q) :=
      fun s F => map_sum (MvPowerSeries.coeff d₂) F s
    rw [hadd, Finset.sum_product]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [MvPowerSeries.coeff_mul]
    rfl
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, rfl⟩ := sumElim_injective2 h1
    obtain ⟨rfl, rfl⟩ := sumElim_injective2 h2
    rfl

def curry [DecidableEq σ] [DecidableEq τ] : MvPowerSeries (σ ⊕ τ) R ≃ₐ[R] MvPowerSeries σ (MvPowerSeries τ R) :=
  AlgEquiv.ofLinearEquiv curryLinearEquiv curryFun_one curryFun_mul

theorem coeff_coeff_curry [DecidableEq σ] [DecidableEq τ] (f : MvPowerSeries (σ ⊕ τ) R) (d₁ : σ →₀ ℕ) (d₂ : τ →₀ ℕ) :
    MvPowerSeries.coeff d₂ (MvPowerSeries.coeff d₁ (curry f)) = MvPowerSeries.coeff (d₁.sumElim d₂) f := rfl

theorem curry_rename_inl [Finite σ] [Finite τ] [DecidableEq σ] [DecidableEq τ] (f : MvPowerSeries σ R) :
    curry (MvPowerSeries.rename (Sum.inl : σ → σ ⊕ τ) f) =
      MvPowerSeries.map (algebraMap R (MvPowerSeries τ R)) f := by
  classical
  refine MvPowerSeries.ext fun d₁ => MvPowerSeries.ext fun d₂ => ?_
  rw [coeff_coeff_curry, MvPowerSeries.coeff_map, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    MvPowerSeries.coeff_C]
  by_cases h : d₂ = 0
  · subst h
    rw [if_pos rfl, ← embDomain_inl]
    exact MvPowerSeries.coeff_embDomain_rename Function.Embedding.inl f d₁
  · rw [if_neg h]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨e, he⟩
    apply h
    have hm : mapDomain Sum.inl e = embDomain (Function.Embedding.inl : σ ↪ σ ⊕ τ) e :=
      (embDomain_eq_mapDomain (Function.Embedding.inl : σ ↪ σ ⊕ τ) e).symm
    have : (d₁.sumElim d₂).comapDomain Sum.inr Sum.inr_injective.injOn = 0 := by
      rw [← he, hm, embDomain_inl, comapDomain_inr_sumElim]
    rwa [comapDomain_inr_sumElim] at this

theorem curry_rename_inr [Finite σ] [Finite τ] [DecidableEq σ] [DecidableEq τ] (g : MvPowerSeries τ R) :
    curry (MvPowerSeries.rename (Sum.inr : τ → σ ⊕ τ) g) = MvPowerSeries.C g := by
  classical
  refine MvPowerSeries.ext fun d₁ => MvPowerSeries.ext fun d₂ => ?_
  rw [coeff_coeff_curry, MvPowerSeries.coeff_C]
  by_cases h : d₁ = 0
  · subst h
    rw [if_pos rfl, ← embDomain_inr]
    exact MvPowerSeries.coeff_embDomain_rename Function.Embedding.inr g d₂
  · rw [if_neg h, MvPowerSeries.coeff_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨e, he⟩
    apply h
    have hm : mapDomain Sum.inr e = embDomain (Function.Embedding.inr : τ ↪ σ ⊕ τ) e :=
      (embDomain_eq_mapDomain (Function.Embedding.inr : τ ↪ σ ⊕ τ) e).symm
    have : (d₁.sumElim d₂).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
      rw [← he, hm, embDomain_inr, comapDomain_inl_sumElim]
    rwa [comapDomain_inl_sumElim] at this

end Curry

namespace Eng
open MvPowerSeries

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

end Eng

section ModCoeff

variable {S : Type u} [CommRing S] {σ : Type v} {ι : Type w} [Fintype ι]
  {A : Type x} [CommRing A] [Algebra S A] (φ : ι → A)

def θ : MvPowerSeries σ A →ₐ[S] MvPowerSeries σ (A ⧸ Ideal.span (Set.range φ)) :=
  MvPowerSeries.mapAlgHom (Ideal.Quotient.mkₐ S (Ideal.span (Set.range φ)))

theorem θ_apply (p : MvPowerSeries σ A) : θ (S := S) (σ := σ) φ p = MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span (Set.range φ))) p := rfl

theorem θ_surjective : Function.Surjective (θ (S := S) (σ := σ) φ) := by
  intro g
  refine ⟨fun d => Function.surjInv Ideal.Quotient.mk_surjective (g d), ?_⟩
  ext d
  rw [θ_apply, MvPowerSeries.coeff_map]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective (g d)

theorem ker_θ : RingHom.ker (θ (S := S) (σ := σ) φ) =
    Ideal.span (Set.range fun i => (MvPowerSeries.C (φ i) : MvPowerSeries σ A)) := by
  classical
  apply le_antisymm
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have hcoef : ∀ d, MvPowerSeries.coeff d p ∈ Submodule.span A (Set.range φ) := fun d => by
      have h := congrArg (MvPowerSeries.coeff d) hp
      rw [map_zero] at h
      change MvPowerSeries.coeff d (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span (Set.range φ))) p) = 0 at h
      rw [MvPowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    choose c hc using fun d => (Submodule.mem_span_range_iff_exists_fun A).1 (hcoef d)
    let g : ι → MvPowerSeries σ A := fun i d => c d i
    have hp' : p = ∑ i, MvPowerSeries.C (φ i) * g i := by
      ext d
      rw [map_sum, ← hc d]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_C_mul, smul_eq_mul, mul_comm]
      rfl
    rw [hp']
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span (Set.range φ))) (MvPowerSeries.C (φ i)) = 0
    rw [MvPowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]

def θbar : (MvPowerSeries σ A ⧸ Ideal.span (Set.range fun i => (MvPowerSeries.C (φ i) : MvPowerSeries σ A))) ≃ₐ[S]
    MvPowerSeries σ (A ⧸ Ideal.span (Set.range φ)) :=
  (Ideal.quotientEquivAlgOfEq S (ker_θ (S := S) (σ := σ) φ)).symm.trans (Ideal.quotientKerAlgEquivOfSurjective (θ_surjective φ))

theorem θbar_mk (p : MvPowerSeries σ A) :
    θbar (S := S) φ (Ideal.Quotient.mk _ p) = MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span (Set.range φ))) p := rfl

end ModCoeff

end TQ

open TQ in
theorem solution
    {S : Type u} [CommRing S] {σ : Type v} [Fintype σ] [DecidableEq σ] {ι : Type w} [Fintype ι]
    (φ : ι → MvPowerSeries σ S)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ S) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ e : (MvPowerSeries (σ ⊕ σ) S ⧸
        Ideal.span (Set.range (fun i => MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) (φ i)) ∪
          Set.range (fun i => MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) (φ i)))) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span (Set.range φ)) ⊗[S] (MvPowerSeries σ S ⧸ Ideal.span (Set.range φ)),
      ∀ f g : MvPowerSeries σ S,
        e (Ideal.Quotient.mk _ (MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) f * MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) g)) =
          Ideal.Quotient.mk (Ideal.span (Set.range φ)) f ⊗ₜ[S] Ideal.Quotient.mk (Ideal.span (Set.range φ)) g := by
  classical

  let A := MvPowerSeries σ S
  let I : Ideal A := Ideal.span (Set.range φ)
  let Q := A ⧸ I
  let Ax := MvPowerSeries σ A
  let κ : MvPowerSeries (σ ⊕ σ) S ≃ₐ[S] Ax := TQ.curry
  let J : Ideal (MvPowerSeries (σ ⊕ σ) S) :=
    Ideal.span (Set.range (fun i => MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) (φ i)) ∪
      Set.range (fun i => MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) (φ i)))
  let I₁ : Ideal Ax := Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap S A) (φ i))
  let Ie : Ideal Ax := Ideal.span (Set.range fun i => (MvPowerSeries.C (φ i) : Ax))

  have hr1 : ((κ : MvPowerSeries (σ ⊕ σ) S →+* Ax) ∘ fun i => MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) (φ i)) =
      fun i => MvPowerSeries.map (algebraMap S A) (φ i) := funext fun i => TQ.curry_rename_inl (τ := σ) (φ i)
  have hr2 : ((κ : MvPowerSeries (σ ⊕ σ) S →+* Ax) ∘ fun i => MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) (φ i)) =
      fun i => (MvPowerSeries.C (φ i) : Ax) := funext fun i => TQ.curry_rename_inr (σ := σ) (φ i)
  have hJ : I₁ ⊔ Ie = J.map (κ : MvPowerSeries (σ ⊕ σ) S →+* Ax) := by
    rw [Ideal.map_span, Set.image_union, ← Set.range_comp, ← Set.range_comp, Ideal.span_union, hr1, hr2]
  let E1 : (MvPowerSeries (σ ⊕ σ) S ⧸ J) ≃ₐ[S] (Ax ⧸ (I₁ ⊔ Ie)) := Ideal.quotientEquivAlg J (I₁ ⊔ Ie) κ hJ

  let E3 : (Ax ⧸ (I₁ ⊔ Ie)) ≃ₐ[S] ((Ax ⧸ Ie) ⧸ I₁.map (Ideal.Quotient.mkₐ S Ie)) :=
    (Ideal.quotientEquivAlgOfEq S (sup_comm I₁ Ie)).trans (DoubleQuot.quotQuotEquivQuotSupₐ S Ie I₁).symm

  let θb : (Ax ⧸ Ie) ≃ₐ[S] MvPowerSeries σ Q := TQ.θbar (S := S) φ
  let Ī : Ideal (MvPowerSeries σ Q) := Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap S Q) (φ i))
  have hcomp : ((θb : (Ax ⧸ Ie) →+* MvPowerSeries σ Q) ∘ (Ideal.Quotient.mkₐ S Ie) ∘ fun i => MvPowerSeries.map (algebraMap S A) (φ i)) =
      fun i => MvPowerSeries.map (algebraMap S Q) (φ i) := by
    funext i
    change MvPowerSeries.map (Ideal.Quotient.mk I) (MvPowerSeries.map (algebraMap S A) (φ i)) = MvPowerSeries.map (algebraMap S Q) (φ i)
    rw [MvPowerSeries.map_map]
    rfl
  have hĪ : Ī = (I₁.map (Ideal.Quotient.mkₐ S Ie)).map (θb : (Ax ⧸ Ie) →+* MvPowerSeries σ Q) := by
    show Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap S Q) (φ i)) = _
    rw [Ideal.map_span, Ideal.map_span, Set.image_image, ← Set.range_comp, ← hcomp]
    rfl
  let E4 : ((Ax ⧸ Ie) ⧸ I₁.map (Ideal.Quotient.mkₐ S Ie)) ≃ₐ[S] (MvPowerSeries σ Q ⧸ Ī) :=
    Ideal.quotientEquivAlg _ Ī θb hĪ

  obtain ⟨N, hN⟩ := hN
  have hpow := TQ.Eng.pow_span_X_le_of_forall_X_pow_mem N I hN
  obtain ⟨e₆, he₆⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le Q φ _ hpow
  let E6 : (MvPowerSeries σ Q ⧸ Ī) ≃ₐ[S] Q ⊗[S] Q := (e₆.symm.restrictScalars S)
  let E7 : Q ⊗[S] Q ≃ₐ[S] Q ⊗[S] Q := Algebra.TensorProduct.comm S Q Q
  refine ⟨(((E1.trans E3).trans E4).trans E6).trans E7, fun f g => ?_⟩

  have h1 : (((E1.trans E3).trans E4)) (Ideal.Quotient.mk J (MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) f * MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) g)) =
      Ideal.Quotient.mk Ī (MvPowerSeries.map (algebraMap S Q) f * MvPowerSeries.C (Ideal.Quotient.mk I g)) := by
    change Ideal.Quotient.mk Ī (θb (Ideal.Quotient.mk Ie (κ (MvPowerSeries.rename Sum.inl f * MvPowerSeries.rename Sum.inr g)))) = _
    rw [map_mul, TQ.curry_rename_inl, TQ.curry_rename_inr, map_mul, map_mul]
    congr 1
    change MvPowerSeries.map (Ideal.Quotient.mk I) (MvPowerSeries.map (algebraMap S A) f) *
      MvPowerSeries.map (Ideal.Quotient.mk I) (MvPowerSeries.C g) = _
    rw [MvPowerSeries.map_map, MvPowerSeries.map_C]
    rfl
  have hsm : ∀ (q : Q) (p : MvPowerSeries σ Q), q • Ideal.Quotient.mk Ī p = Ideal.Quotient.mk Ī (MvPowerSeries.C q * p) :=
    fun q p => by rw [← MvPowerSeries.smul_eq_C_mul]; rfl
  have h2 : e₆ (Ideal.Quotient.mk I g ⊗ₜ[S] Ideal.Quotient.mk I f) =
      Ideal.Quotient.mk Ī (MvPowerSeries.map (algebraMap S Q) f * MvPowerSeries.C (Ideal.Quotient.mk I g)) := by
    rw [he₆, mul_comm]
    exact hsm _ _
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, h1]
  change Algebra.TensorProduct.comm S Q Q (e₆.symm (Ideal.Quotient.mk Ī _)) = _
  rw [← h2, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.comm_tmul]

end
end S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename
end P2MW
export P2MW.S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename (solution)
