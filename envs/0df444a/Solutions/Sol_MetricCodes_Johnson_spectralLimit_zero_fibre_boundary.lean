-- Prove2me | solution 1 for MetricCodes.Johnson.spectralLimit_zero_fibre_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/6b101287-565d-4e3c-aad1-43207c5d6079

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_sqrt_one_sub_centeredDegree_sq
import Theorems.Thm_MetricCodes_Johnson_zero_fibre_spectral_algebra

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2) :
    1 - spectralLimit α 0 0 u =
      (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  let z : ℝ := centeredDegree u
  let m : ℝ := centeredWeight α
  let s : ℝ := Real.sqrt (u * (1 - u))
  have ha0 : 0 < α := lt_trans hu hua
  have haone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvariance : 0 < u * (1 - u) := mul_pos hu huone
  have hz : z ≠ 0 := by
    dsimp [z, centeredDegree]
    nlinarith
  have hm : 1 - m ^ 2 ≠ 0 := by
    have hprod : 0 < α * (1 - α) := mul_pos ha0 haone
    dsimp [m, centeredWeight]
    nlinarith
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_pos.mpr hvariance).ne'
  have hplus : 1 + 2 * s ≠ 0 := by
    have hsnonneg : 0 ≤ s := by
      dsimp [s]
      exact Real.sqrt_nonneg _
    nlinarith
  have hsquare : 4 * s ^ 2 = 1 - z ^ 2 := by
    have hsqrt := Real.sq_sqrt hvariance.le
    dsimp [s, z, centeredDegree]
    nlinarith
  have hradical : Real.sqrt (1 - z ^ 2) = 2 * s := by
    simpa [z, s] using
      sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hsig : centeredSigma 0 0 = 1 := by
    norm_num [centeredSigma]
  have heta : centeredEta α 0 0 = centeredWeight α := by
    simp [centeredEta, centeredWeight]
  have hlimit :
      spectralLimit α 0 0 u =
        (m - m * z ^ 2) ^ 2 /
            (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s)) := by
    change
      ((centeredSigma 0 0 * centeredEta α 0 0 -
          centeredWeight α * centeredDegree u ^ 2) ^ 2 /
        (centeredDegree u ^ 2 *
          (1 - centeredWeight α ^ 2) *
          (1 - centeredDegree u ^ 2)) +
        ((centeredDegree u ^ 2 - centeredEta α 0 0 ^ 2) *
          (centeredSigma 0 0 ^ 2 - centeredDegree u ^ 2)) /
          (centeredDegree u ^ 2 *
            (1 - centeredWeight α ^ 2) *
            Real.sqrt (1 - centeredDegree u ^ 2))) = _
    rw [hsig, heta]
    simp only [one_mul, one_pow]
    change
      (m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) = _
    rw [hradical]
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos ha0 haone).ne'
  have hfourA : α * 4 - α ^ 2 * 4 ≠ 0 := by
    have hp : 0 < α * (1 - α) := mul_pos ha0 haone
    nlinarith
  have hmraw : 1 - (1 - 2 * α) ^ 2 ≠ 0 := by
    simpa [m, centeredWeight] using hm
  have hplusraw :
      1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    simpa [s] using hplus
  calc
    1 - spectralLimit α 0 0 u =
        (z ^ 2 - m ^ 2) /
          ((1 - m ^ 2) * (1 + 2 * s)) := by
      rw [hlimit]
      exact zero_fibre_spectral_algebra z m s hz hm hs hplus hsquare
    _ = (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
      dsimp [z, m, s, centeredDegree, centeredWeight]
      field_simp [hmraw, hA, hfourA, hplusraw]
      ; ring
end MetricCodes.Johnson
