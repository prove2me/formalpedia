-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_coeff_eq_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:10:03.521285+00:00
-- url     : https://prove2.me/submissions/32518b43-c103-4d87-b836-99ab44d96dd8

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_subst_finsum_seriesShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_monomial_coeff_eq_zero
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finsum_eq_sum_subtype_of_vanish_outside

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

/-- **Finite-sum form of a sheared coefficient.**  For truncation data `T`, `delta` with
`delta i` vanishing in degrees below `T i` and `u i ≤ T i * v0`, every retained coefficient of the
substituted series is the finite simplex sum of the retained source coefficients weighted by the
corresponding sheared-monomial coefficients. -/
theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (T : Fin m → ℕ) (delta : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hT : ∀ i, u i ≤ (T i : ℝ) * v0)
    (hdelta : ∀ i (n : ℕ), n < T i → PowerSeries.coeff n (delta i) = 0)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (a : ↥(strictWeightedSimplex (Fin.cases v0 u) H)) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ + liftLogSeries m (delta i))) F) =
      ∑ b : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
            (formalShear delta
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector b.val) 1)) *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val) F := by
  classical
  -- The truncation orders are positive: `0 < u i ≤ T i * v0` with `v0 > 0`.
  have hTpos : ∀ i, 0 < T i := by
    intro i
    have h3 : (0 : ℝ) < (T i : ℝ) := by
      nlinarith [hu i, hT i, hv0]
    exact_mod_cast h3
  have hD0 : ∀ i, PowerSeries.coeff 0 (delta i) = 0 := by
    intro i
    exact hdelta i 0 (hTpos i)
  -- The coefficient of the substituted series as an unrestricted finsum.
  have hexp := coeff_subst_finsum_seriesShear (D := delta) hD0 F a.val
  -- Summands indexed by exponents outside the strict simplex vanish.
  have hzero : ∀ x : Fin (m + 1) → ℕ, x ∉ strictWeightedSimplex (Fin.cases v0 u) H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector x) F *
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (seriesShear delta
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector x) 1)) = 0 := by
    intro x hx
    have hform :=
      weightedShear_monomial_coeff_eq_zero v0 u H T delta hv0 hu hT hdelta F a x hx
    have hser : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
        (seriesShear delta
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector x) 1)) = 0 := by
      simpa only [seriesShear, formalShear] using hform
    rw [hser, mul_zero]
  rw [hexp]
  rw [finsum_eq_sum_subtype_of_vanish_outside
    (strictWeightedSimplex (Fin.cases v0 u) H)
    (fun x => MvPowerSeries.coeff (InterpolationMatrix.exponentVector x) F *
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
        (seriesShear delta
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector x) 1))) hzero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [seriesShear, formalShear, mul_comm]
