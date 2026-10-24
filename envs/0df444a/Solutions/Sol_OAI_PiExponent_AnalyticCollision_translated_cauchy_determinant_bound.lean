-- Prove2me | solution 1 for OAI.PiExponent.AnalyticCollision.translated_cauchy_determinant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T05:10:06.154499+00:00
-- url     : https://prove2.me/submissions/df22fcec-27d3-4b31-abd5-6ba5bb93846c

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Theorems.Thm_OAI_PiExponent_AnalyticCollision_norm_normalizedTaylorCoeff_le
import Theorems.Thm_OAI_PiExponent_AnalyticCollision_norm_rowTest_shifted_power_le
import Theorems.Thm_OAI_PiExponent_AnalyticCollision_hasSum_translated_row
import Theorems.Thm_OAI_PiExponent_AnalyticCollision_infinite_collision_bound
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (F : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ)
    (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1) (hss : s * s = 1 / 2)
    (hF : ∀ a j, Differentiable ℂ (F a j))
    (hFD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖F a j z‖ ≤ D)
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun i j =>
      cauchyPowerSeries
        (fun t : ℂ => F (group i) j (center i + Complex.log (1 + t)))
        0 (1 / 2) (ell i) (fun _ => (1 : ℂ)) )‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι *
        (2 : ℝ) ^ (∑ i, ell i)) *
        s ^ (∑ a, (multiplicity group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let B : ι → ℕ → ℂ := fun i d =>
    cauchyPowerSeries
      (fun t : ℂ => (((center i + Complex.log (1 + t)) / (R : ℂ)) ^ d))
      0 (1 / 2) (ell i) (fun _ => (1 : ℂ))
  let C : κ → ℕ → ι → ℂ := fun a d j =>
    cauchyPowerSeries (F a j) 0 (R : ℝ) d (fun _ => (R : ℂ))
  let A : Matrix ι ι ℂ := fun i j =>
    cauchyPowerSeries
      (fun t : ℂ => F (group i) j (center i + Complex.log (1 + t)))
      0 (1 / 2) (ell i) (fun _ => (1 : ℂ))
  have hC : ∀ a d j, ‖C a d j‖ ≤ D := by
    intro a d j
    exact OAI.PiExponent.AnalyticCollision.norm_normalizedTaylorCoeff_le
      (by exact_mod_cast hR) (hFD a j) d
  have hB : ∀ i d, ‖B i d‖ ≤ (2 : ℝ) ^ ell i * (s * s) ^ d := by
    intro i d
    dsimp [B]
    rw [hss]
    exact OAI.PiExponent.AnalyticCollision.norm_rowTest_shifted_power_le
      (by exact_mod_cast hR) (hc i) (ell i) d
  have hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (A i j) := by
    intro i j
    exact OAI.PiExponent.AnalyticCollision.hasSum_translated_row
      (hF (group i) j) hR hD (hFD (group i) j) (hc i) (ell i)
  have hbound := OAI.PiExponent.AnalyticCollision.infinite_collision_bound
    group B C A D s (fun i => (2 : ℝ) ^ ell i) hD hs0 hs1
    (by intro i; positivity) hC hB hsum
  simpa [A, Finset.prod_pow_eq_pow_sum] using hbound
