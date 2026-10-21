-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_comp_of_weightedOrder
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:43:47.549564+00:00
-- url     : https://prove2.me/submissions/deb483c5-5148-463f-a0e3-31d41b03f62d

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_liftLogSeries_of_X_zero
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_monomial_coeff_eq_zero_of_weight_lt
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_coordinate_roundtrip
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

set_option maxHeartbeats 1200000

/-- The weighted shear matrices satisfy the addition law for the shears. -/
theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D E : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hE : ∀ i n, n < N i → PowerSeries.coeff n (E i) = 0) :
    (weightedShear (m := m) v0 u H E) ∘ₗ
        (weightedShear (m := m) v0 u H D) =
      weightedShear (m := m) v0 u H (fun i : Fin m => D i + E i) := by
  classical
  -- the weights and the strict simplex in the shapes used below
  let w : Fin (m + 1) → ℝ := fun i => Fin.cases v0 u i
  let S : Finset (Fin (m + 1) → ℕ) := strictWeightedSimplex w H
  let q : Fin (m + 1) → ℝ := w
  have hq : ∀ j, 0 < q j := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa [q, w] using hv0
    · intro i; simpa [q, w] using hu i
  by_cases hH : 0 < H
  · -- the main case: the simplex may be non-empty
    -- the three substitution families
    let famE : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
      fun i => Fin.cases (MvPowerSeries.X 0)
        (fun j => MvPowerSeries.X j.succ + liftLogSeries m (E j)) i
    let famD : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
      fun i => Fin.cases (MvPowerSeries.X 0)
        (fun j => MvPowerSeries.X j.succ + liftLogSeries m (D j)) i
    let famDE : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
      fun i => Fin.cases (MvPowerSeries.X 0)
        (fun j => MvPowerSeries.X j.succ + liftLogSeries m (D j + E j)) i
    have hfamD : seriesShear (m := m) D = MvPolynomial.aeval famD := rfl
    have hfamDE : seriesShear (m := m) (fun i : Fin m => D i + E i) =
        MvPolynomial.aeval famDE := rfl
    -- the matrix entries are the sheared monomial coefficients
    have happ : ∀ (F' : Fin m → PowerSeries ℂ) (z : ↥S → ℂ) (c : ↥S),
        weightedShear (m := m) v0 u H F' z c =
          ∑ a : ↥S, z a * MvPowerSeries.coeff
            (InterpolationMatrix.exponentVector c.val)
            (seriesShear (m := m) F'
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) := by
      intro F' z c
      rfl
    -- `E` has no constant terms because of the support hypothesis
    have hNpos : ∀ i, 0 < N i := by
      intro i
      have h1 : (0 : ℝ) < (N i : ℝ) := by nlinarith [hu i, hN i, hv0]
      exact_mod_cast h1
    have hE0 : ∀ i, PowerSeries.coeff 0 (E i) = 0 := fun i => hE i 0 (hNpos i)
    -- the `q`-shaped support hypothesis for `E`
    have hEq : ∀ i : Fin m, ∀ n : ℕ,
        (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (E i) = 0 := by
      intro i n hn
      have hq0 : q 0 = v0 := rfl
      have hqi : q i.succ = u i := rfl
      rw [hq0, hqi] at hn
      refine hE i n ?_
      by_contra hlt
      push Not at hlt
      have hle : (N i : ℝ) * v0 ≤ (n : ℝ) * v0 := by
        have hNle : (N i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt
        exact mul_le_mul_of_nonneg_right hNle hv0.le
      linarith [hN i]
    -- hence the forward family of `E` is substitutable
    have hsubE : MvPowerSeries.HasSubst famE :=
      (OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_roundtrip
        (q := q) hq E hEq).1
    have hfamE0 : famE 0 = MvPowerSeries.X 0 := rfl
    -- composition of the two substitutions is the substitution of `D + E`
    have hcomp : ∀ Q : MvPolynomial (Fin (m + 1)) ℂ,
        MvPowerSeries.subst famE (MvPolynomial.aeval famD Q) =
          MvPolynomial.aeval famDE Q := by
      intro Q
      have hhom : (MvPowerSeries.substAlgHom hsubE).comp (MvPolynomial.aeval famD) =
          MvPolynomial.aeval famDE := by
        apply MvPolynomial.algHom_ext
        intro i
        rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
        refine Fin.cases ?_ ?_ i
        · simp only [famD, famE, famDE, Fin.cases_zero]
          rw [MvPowerSeries.substAlgHom_X hsubE]
          rfl
        · intro j
          simp only [famD, famDE, Fin.cases_succ]
          rw [map_add, map_add (liftLogSeries m) (D j) (E j)]
          rw [MvPowerSeries.substAlgHom_X hsubE]
          rw [MvPowerSeries.substAlgHom_apply hsubE]
          rw [subst_liftLogSeries_of_X_zero (D j) famE hsubE hfamE0]
          simp only [famE, Fin.cases_succ]
          ring
      have hQ := congrArg (fun f : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
        MvPowerSeries (Fin (m + 1)) ℂ => f Q) hhom
      simpa using hQ
    -- the forward shear of `E` is weight non-decreasing
    have htri : ∀ (a b : Fin (m + 1) → ℕ),
        (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
          (∑ i, Fin.cases v0 u i * (a i : ℝ)) →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
          (seriesShear (m := m) E
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by
      intro a b hab
      exact OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_monomial_coeff_eq_zero_of_weight_lt
        (v0 := v0) (u := u) (N := N) (D := E) hv0 hu hN hE a b hab
    apply LinearMap.ext
    intro x
    funext b
    -- the polynomial whose sheared coefficients are `W(D) x`
    let Px : MvPolynomial (Fin (m + 1)) ℂ :=
      ∑ a : ↥S, x a • MvPolynomial.monomial
        (InterpolationMatrix.exponentVector a.val) (1 : ℂ)
    let F : MvPowerSeries (Fin (m + 1)) ℂ := MvPolynomial.aeval famD Px
    let y : ↥S → ℂ := fun a =>
      ∑ a' : ↥S, x a' * MvPowerSeries.coeff
        (InterpolationMatrix.exponentVector a.val)
        (seriesShear (m := m) D
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a'.val) (1 : ℂ)))
    have hy : ∀ a : ↥S, (weightedShear (m := m) v0 u H D) x a = y a := by
      intro a
      rw [happ D]
    have hF : ∀ a : ↥S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) F = y a := by
      intro a
      simp only [F, Px, y]
      rw [map_sum]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [← hfamD]
    have hLin : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (MvPolynomial.aeval famDE Px) =
        ∑ a : ↥S, x a * MvPowerSeries.coeff
          (InterpolationMatrix.exponentVector b.val)
          (seriesShear (m := m) (fun i : Fin m => D i + E i)
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) := by
      simp only [Px]
      rw [map_sum]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [← hfamDE]
    have hcompF : MvPowerSeries.subst famE F = MvPolynomial.aeval famDE Px := hcomp Px
    have hExpand : (∑ a : ↥S,
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) F *
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
              (seriesShear (m := m) E
                (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ)))) =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (MvPowerSeries.subst famE F) := by
      have hexp :=
        OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
          (v0 := v0) (u := u) (H := H) (D := E) hv0 hu hH hE0 htri F b
      simpa [S, w, famE] using hexp
    rw [LinearMap.comp_apply]
    calc (weightedShear (m := m) v0 u H E) ((weightedShear (m := m) v0 u H D) x) b
        = ∑ a : ↥S, ((weightedShear (m := m) v0 u H D) x) a *
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
              (seriesShear (m := m) E
                (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) :=
          happ E ((weightedShear (m := m) v0 u H D) x) b
      _ = ∑ a : ↥S, y a *
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
              (seriesShear (m := m) E
                (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hy a]
      _ = ∑ a : ↥S,
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) F *
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
              (seriesShear (m := m) E
                (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hF a]
      _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
            (MvPowerSeries.subst famE F) := hExpand
      _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
            (MvPolynomial.aeval famDE Px) := by rw [hcompF]
      _ = ∑ a : ↥S, x a * MvPowerSeries.coeff
            (InterpolationMatrix.exponentVector b.val)
            (seriesShear (m := m) (fun i : Fin m => D i + E i)
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) := hLin
      _ = (weightedShear (m := m) v0 u H (fun i : Fin m => D i + E i)) x b :=
          (happ (fun i : Fin m => D i + E i) x b).symm
  · -- if `H ≤ 0` the simplex is empty and both operators are trivial
    apply LinearMap.ext
    intro x
    funext b
    have hbH : (∑ i, w i * (b.val i : ℝ)) < H := by
      have h := (Finset.mem_filter.mp b.property).2
      simpa [S] using h
    have hnonneg : 0 ≤ ∑ i, w i * (b.val i : ℝ) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (le_of_lt (hq i)) (Nat.cast_nonneg _)
    linarith
