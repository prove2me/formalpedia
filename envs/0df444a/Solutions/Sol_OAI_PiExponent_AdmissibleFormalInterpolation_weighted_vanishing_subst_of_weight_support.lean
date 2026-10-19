-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_of_weight_support
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T19:19:05.219986+00:00
-- url     : https://prove2.me/submissions/3c95c92e-ea51-45a3-8080-a71dc268e4ca

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Weight

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

-- A coefficient of 1 is supported only at the zero exponent.
private theorem real_weight_support_one {σ : Type*}
    (W : (σ →₀ ℕ) →+ ℝ) :
    ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d (1 : MvPowerSeries σ ℂ) ≠ 0 → 0 ≤ W d := by
  classical
  intro d hd
  have hd0 : d = 0 := by
    by_contra h
    exact hd (by simp only [MvPowerSeries.coeff_one, if_neg h])
  subst d
  simp

-- Lower bounds on additive exponent weights add under multiplication.
private theorem real_weight_support_mul {σ : Type*}
    (W : (σ →₀ ℕ) →+ ℝ) (f g : MvPowerSeries σ ℂ) (u v : ℝ)
    (hf : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff d f ≠ 0 → u ≤ W d)
    (hg : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff d g ≠ 0 → v ≤ W d) :
    ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d (f * g) ≠ 0 → u + v ≤ W d := by
  classical
  intro d hd
  by_contra h
  apply hd
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  by_cases ha : MvPowerSeries.coeff a f = 0
  · simp only [ha, zero_mul]
  by_cases hb : MvPowerSeries.coeff b g = 0
  · simp only [hb, mul_zero]
  have bound := add_le_add (hf a ha) (hg b hb)
  rw [← map_add W a b, hab'] at bound
  exact False.elim (h bound)

private theorem real_weight_support_pow {σ : Type*}
    (W : (σ →₀ ℕ) →+ ℝ) (f : MvPowerSeries σ ℂ) (u : ℝ)
    (hf : ∀ d : σ →₀ ℕ, MvPowerSeries.coeff d f ≠ 0 → u ≤ W d)
    (n : ℕ) :
    ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d (f ^ n) ≠ 0 → (n : ℝ) * u ≤ W d := by
  induction n with
  | zero =>
      simpa only [pow_zero, Nat.cast_zero, zero_mul] using real_weight_support_one W
  | succ n ih =>
      simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using
        real_weight_support_mul W (f ^ n) f ((n : ℝ) * u) u ih hf

private theorem real_weight_support_prod {σ ι : Type*}
    (W : (σ →₀ ℕ) →+ ℝ) (s : Finset ι)
    (g : ι → MvPowerSeries σ ℂ) (b : ι → ℝ) :
    (∀ i ∈ s, ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d (g i) ≠ 0 → b i ≤ W d) →
    ∀ d : σ →₀ ℕ,
      MvPowerSeries.coeff d (∏ i ∈ s, g i) ≠ 0 →
      (∑ i ∈ s, b i) ≤ W d := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro hg
      simpa only [Finset.prod_empty, Finset.sum_empty] using real_weight_support_one W
  | @insert i s hi ih =>
      intro hg
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact real_weight_support_mul W (g i) (∏ j ∈ s, g j) (b i) (∑ j ∈ s, b j)
        (hg i (Finset.mem_insert_self i s))
        (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

-- The general finite-variable statement, now proved rather than imported as a child.
theorem OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_finsupp
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : σ → ℝ)
    (φ : σ → MvPowerSeries σ ℂ)
    (hq : ∀ i, 0 < q i)
    (hφ : ∀ (i : σ) (d : σ →₀ ℕ),
      MvPowerSeries.coeff d (φ i) ≠ 0 →
      q i ≤ ∑ j, q j * (d j : ℝ))
    (H : ℝ) (F : MvPowerSeries σ ℂ)
    (hF : ∀ d : σ →₀ ℕ,
      (∑ i, q i * (d i : ℝ)) < H →
      MvPowerSeries.coeff d F = 0) :
    ∀ e : σ →₀ ℕ,
      (∑ i, q i * (e i : ℝ)) < H →
      MvPowerSeries.coeff e (MvPowerSeries.subst φ F) = 0 := by
  classical
  let W : (σ →₀ ℕ) →+ ℝ := Finsupp.weight q
  have hW (d : σ →₀ ℕ) : W d = ∑ i, q i * (d i : ℝ) := by
    calc
      W d = ∑ i, (d i : ℝ) * q i := by
        simp only [W, Finsupp.weight_eq_sum, nsmul_eq_mul]
      _ = ∑ i, q i * (d i : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
  have hφW : ∀ (i : σ) (d : σ →₀ ℕ),
      MvPowerSeries.coeff d (φ i) ≠ 0 → q i ≤ W d := by
    intro i d hd
    rw [hW d]
    exact hφ i d hd
  have hc : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := by
    intro i
    by_contra hi
    have hzero : MvPowerSeries.coeff (0 : σ →₀ ℕ) (φ i) ≠ 0 := by
      simpa only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hi
    have hb : q i ≤ 0 := by simpa only [map_zero] using hφW i 0 hzero
    exact (not_le_of_gt (hq i)) hb
  have hs : MvPowerSeries.HasSubst φ :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  intro e he
  rw [MvPowerSeries.coeff_subst hs F e]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : MvPowerSeries.coeff d F = 0
  · simp only [hd, zero_smul]
  have hHd : H ≤ W d := by
    by_contra h
    apply hd
    apply hF d
    rw [← hW d]
    exact lt_of_not_ge h
  have heWd : W e < W d :=
    lt_of_lt_of_le (by simpa only [hW e] using he) hHd
  have hprod0 : MvPowerSeries.coeff e (d.prod fun i n => φ i ^ n) = 0 := by
    by_contra hprod
    have hp : (∑ i ∈ d.support, (d i : ℝ) * q i) ≤ W e :=
      real_weight_support_prod W d.support (fun i => φ i ^ d i)
        (fun i => (d i : ℝ) * q i)
        (fun i _ => real_weight_support_pow W (φ i) (q i) (hφW i) (d i))
        e (by simpa only [Finsupp.prod] using hprod)
    have hWd : W d = ∑ i ∈ d.support, (d i : ℝ) * q i := by
      simp only [W, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
    rw [← hWd] at hp
    exact (not_le_of_gt heWd) hp
  simp only [hprod0, smul_zero]

theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ)
    (φ : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hq : ∀ i, 0 < q i)
    (hφ : ∀ (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ i) ≠ 0 →
      q i ≤ ∑ j, q j * (a j : ℝ))
    (H : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, q i * (a i : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst φ F) = 0 := by
  intro a ha
  have hφ' : ∀ (i : Fin (m + 1)) (d : (Fin (m + 1) →₀ ℕ)),
      MvPowerSeries.coeff d (φ i) ≠ 0 →
      q i ≤ ∑ j, q j * (d j : ℝ) := by
    intro i d hd
    have h := hφ i (Finsupp.equivFunOnFinite d)
    have hd' : MvPowerSeries.coeff
        (InterpolationMatrix.exponentVector (Finsupp.equivFunOnFinite d)) (φ i) ≠ 0 := by
      simpa [InterpolationMatrix.exponentVector] using hd
    have hb := h hd'
    simpa [InterpolationMatrix.exponentVector] using hb
  have hF' : ∀ d : (Fin (m + 1) →₀ ℕ),
      (∑ i, q i * (d i : ℝ)) < H →
      MvPowerSeries.coeff d F = 0 := by
    intro d hd
    have h := hF (Finsupp.equivFunOnFinite d)
    simpa [InterpolationMatrix.exponentVector] using h hd
  have h := OAI.PiExponent.AdmissibleFormalInterpolation.weighted_vanishing_subst_finsupp
    q φ hq hφ' H F hF' (InterpolationMatrix.exponentVector a)
      (by simpa [InterpolationMatrix.exponentVector] using ha)
  simpa using h