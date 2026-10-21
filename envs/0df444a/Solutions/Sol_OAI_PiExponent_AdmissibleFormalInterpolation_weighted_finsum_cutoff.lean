-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weighted_finsum_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:59:46.007336+00:00
-- url     : https://prove2.me/submissions/8666b3fd-a38d-4453-87af-ddc0ba39d932

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finsum_eq_sum_subtype_of_vanish_outside
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weight_mem_strictWeightedSimplex
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

/-- Weight triangularity truncates the shear coefficient expansion: for a strict-simplex exponent
vector `b`, only the finitely many `a` inside the strict weighted simplex contribute to the shear
expansion, because every other coefficient vanishes by triangularity. -/
theorem solution {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i) (hH : 0 < H)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (htri : ∀ (a b : Fin (m + 1) → ℕ),
      (∑ i, Fin.cases v0 u i * (b i : ℝ)) <
        (∑ i, Fin.cases v0 u i * (a i : ℝ)) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
        (seriesShear D
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)) = 0)
    (G : MvPowerSeries (Fin (m + 1)) ℂ)
    (b : ↥(strictWeightedSimplex (Fin.cases v0 u) H)) :
    (∑ᶠ a : Fin (m + 1) → ℕ,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) G *
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (seriesShear D
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1))) =
      (∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val) G *
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
            (seriesShear D
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))) := by
  classical
  -- `b` has weighted degree below `H`
  have hbH : (∑ i, Fin.cases v0 u i * (b.val i : ℝ)) < H := by
    have h : b.val ∈ (realWeightedSimplex (Fin.cases v0 u) H).filter
        (fun a => ∑ i, Fin.cases v0 u i * (a i : ℝ) < H) := by
      simpa only [OAI.PiExponent.strictWeightedSimplex] using b.2
    exact (Finset.mem_filter.mp h).2
  -- anything outside the strict simplex has weighted degree at least `H`
  have hout : ∀ a : Fin (m + 1) → ℕ, a ∉ strictWeightedSimplex (Fin.cases v0 u) H →
      H ≤ ∑ i, Fin.cases v0 u i * (a i : ℝ) := by
    intro a ha
    by_contra hcon
    push_neg at hcon
    exact ha (OAI.PiExponent.AdmissibleFormalInterpolation.weight_mem_strictWeightedSimplex
      v0 u H hv0 hu hH a hcon)
  -- reduce the infinite sum to the simplex sum
  refine OAI.PiExponent.AdmissibleFormalInterpolation.finsum_eq_sum_subtype_of_vanish_outside
    (strictWeightedSimplex (Fin.cases v0 u) H)
    (fun a => MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) G *
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (seriesShear D (MvPolynomial.monomial (InterpolationMatrix.exponentVector a) 1)))
    ?_
  intro a ha
  have hle : (∑ i, Fin.cases v0 u i * (b.val i : ℝ)) <
      (∑ i, Fin.cases v0 u i * (a i : ℝ)) := lt_of_lt_of_le hbH (hout a ha)
  rw [htri a b.val hle, mul_zero]
