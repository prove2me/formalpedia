-- Prove2me | solution 2 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:21:32.986467+00:00
-- url     : https://prove2.me/submissions/d43d79c1-714b-4612-9a88-faf069af9ab3

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_monomial_coeff_eq_zero_of_weight_lt
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_subst_seriesJet

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (e : Fin (m + 1) →₀ ℕ) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F
          (MvPolynomial.monomial e 1)) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i)
        (MvPolynomial.monomial e 1) := by
  classical
  have hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0 := by
    intro i
    apply hD i 0
    by_contra hn
    have hNi : N i = 0 := Nat.eq_zero_of_not_pos hn
    have hi := hN i
    simp only [hNi, Nat.cast_zero, zero_mul] at hi
    exact (not_le_of_gt (hu i)) hi
  have htri : ∀ (a b : Fin (m + 1) → ℕ),
      (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
        (∑ i, Fin.cases v0 u i * (a i : ℝ)) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (seriesShear D
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0 := by
    intro a b hab
    exact seriesShear_monomial_coeff_eq_zero_of_weight_lt
      v0 u N D hv0 hu hN hD a b hab
  funext b
  change (∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (seriesJet c F (MvPolynomial.monomial e 1)) *
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (seriesShear D
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))) =
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
      (seriesJet c (fun i => F i + D i) (MvPolynomial.monomial e 1))
  calc
    _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)))
          (seriesJet c F (MvPolynomial.monomial e 1))) :=
      seriesShear_coeff_subst_eq_sum_of_weight_nondecreasing
        v0 u H D hv0 hu hH hD0 htri
        (seriesJet c F (MvPolynomial.monomial e 1)) b
    _ = _ := congrArg (MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val))
      (seriesShear_subst_seriesJet D F c hD0 (MvPolynomial.monomial e 1))
