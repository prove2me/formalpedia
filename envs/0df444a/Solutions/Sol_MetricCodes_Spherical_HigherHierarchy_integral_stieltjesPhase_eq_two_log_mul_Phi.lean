-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.integral_stieltjesPhase_eq_two_log_mul_Phi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/28587fb7-0154-460e-bae5-3d8385ee33eb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_eq_logAtom_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ)
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (ha : ∀ i : Fin (r + 1),
      Integrable (stieltjesLogAtom (quadraticCoordinate (a i))) μ)
    (hb : ∀ i : Fin r,
      Integrable (stieltjesLogAtom (quadraticCoordinate (b i))) μ)
    (hma : ∀ i : Fin (r + 1),
      (∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (a i)) t ∂μ) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy (a i))
    (hmb : ∀ i : Fin r,
      (∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (b i)) t ∂μ) =
        2 * Real.log 2 * MetricCodes.sphericalEntropy (b i)) :
    (∫ t : ℝ, stieltjesPhase a b t ∂μ) =
      2 * Real.log 2 * Phi a b := by
  have hasum : Integrable (fun t : ℝ =>
      ∑ i : Fin (r + 1),
        stieltjesLogAtom (quadraticCoordinate (a i)) t) μ :=
    integrable_finsetSum _ (fun i _ => ha i)
  have hbsum : Integrable (fun t : ℝ =>
      ∑ i : Fin r,
        stieltjesLogAtom (quadraticCoordinate (b i)) t) μ :=
    integrable_finsetSum _ (fun i _ => hb i)
  calc
    (∫ t : ℝ, stieltjesPhase a b t ∂μ) =
        ∫ t : ℝ,
          ((∑ i : Fin (r + 1),
            stieltjesLogAtom (quadraticCoordinate (a i)) t) -
              ∑ i : Fin r,
                stieltjesLogAtom (quadraticCoordinate (b i)) t) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpositive] with t ht
          exact stieltjesPhase_eq_logAtom_sum h ht
    _ = (∑ i : Fin (r + 1),
          ∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (a i)) t ∂μ) -
            ∑ i : Fin r,
              ∫ t : ℝ, stieltjesLogAtom (quadraticCoordinate (b i)) t ∂μ := by
          rw [integral_sub hasum hbsum,
            integral_finsetSum _ (fun i _ => ha i),
            integral_finsetSum _ (fun i _ => hb i)]
    _ = 2 * Real.log 2 * Phi a b := by
          simp_rw [hma, hmb]
          unfold Phi
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          ring
end MetricCodes.Spherical.HigherHierarchy
