-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_coefficient_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:00:58.55462+00:00
-- url     : https://prove2.me/submissions/461c9840-f563-4f5c-8f0c-b1bf039bf637

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_translated_row_determinant_exp_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_periodMonomial_coeff_eq_rowTest
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_columnFunction_norm_le

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {m : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0)
    (hv0 : 0 < v0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * (h c : ℝ) + ∑ i, w i * (a c i : ℝ) ≤ H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((periodMonomial (j r) (h c) (a c)).coeff (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A : κ,
          (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (100 * (K : ℝ) / w0 + Real.log 2 / v0 +
            Real.log (200 * (K : ℝ)) / wstar +
            Collision.collisionRemainder (Fintype.card ι) H)) := by
  let R : NNReal := ⟨100 * (K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < 100 * K; positivity
  have hR1 : (1 : ℝ) ≤ R := by
    change (1 : ℝ) ≤ 100 * K
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hf : ∀ A c, Differentiable ℂ (columnFunction (h c) (a c) (transverse A)) := by
    intro A c
    exact CollisionAnalytic.differentiable_columnFunction _ _ _
  have hfD : ∀ A c z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖columnFunction (h c) (a c) (transverse A) z‖ ≤
        Real.exp (H * ((R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar)) := by
    intro A c z hz
    exact period_columnFunction_norm_le (h c) (a c) (transverse A) w hR1 hH.le
      hw0 hws hw (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le)
  have hc : ∀ r, ‖(j r : ℂ) * OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period‖ + 3 / 4 ≤
      (R : ℝ) / 2 := by
    intro r
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hjK : (j r : ℝ) ≤ K := by exact_mod_cast (hj r).le
    have hnorm : ‖(j r : ℂ) * OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period‖ =
        (j r : ℝ) * (2 * Real.pi) := by
      rw [OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
    rw [hnorm]
    change (j r : ℝ) * (2 * Real.pi) + 3 / 4 ≤ 100 * K / 2
    have hmul := mul_le_mul_of_nonneg_left hjK (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith
  have hb := translated_row_determinant_exp_bound
    group (fun A c => columnFunction (h c) (a c) (transverse A))
    (fun r => (j r : ℂ) * OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period) ell R hR hH
    hf (budgetCoeff := (R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar) (v := v0)
    hfD hc hell
  have hRv : (R : ℝ) = 100 * K := rfl
  rw [hRv] at hb
  have he : (2 : ℝ) * (100 * K) = 200 * K := by ring
  rw [he] at hb
  simp_rw [periodMonomial_coeff_eq_rowTest]
  simpa only [columnFunction, add_assoc, add_left_comm, add_comm] using hb