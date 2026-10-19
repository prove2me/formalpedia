-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.normalizedNu_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/25cb5db1-8dea-4441-a6d2-977c4679a63b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    (N J M eta sigma : ℝ)
    (hN : 0 < N) (hstep : 0 < 2 * J - 1) :
    (Real.sqrt
        ((J ^ 2 - M ^ 2) *
          (J ^ 2 - eta ^ 2) *
          ((sigma + 1) ^ 2 - J ^ 2)) /
      (2 * J * Real.sqrt ((2 * J - 1) * (2 * J + 1)))) / N =
      normalizedNu
        (J / N) (M / N) (eta / N) (sigma / N) (1 / N) := by
  have hrad :
      (J ^ 2 - M ^ 2) *
          (J ^ 2 - eta ^ 2) *
          ((sigma + 1) ^ 2 - J ^ 2) =
        (N ^ 3) ^ 2 *
          (((J / N) ^ 2 - (M / N) ^ 2) *
            ((J / N) ^ 2 - (eta / N) ^ 2) *
            (((sigma / N + 1 / N) ^ 2 - (J / N) ^ 2))) := by
    field_simp [hN.ne']

  have hdenrad :
      (2 * J - 1) * (2 * J + 1) =
        N ^ 2 *
          ((2 * (J / N) - 1 / N) *
            (2 * (J / N) + 1 / N)) := by
    field_simp [hN.ne']

  have hJ : 0 < J := by linarith
  have hleft : 0 < 2 * (J / N) - 1 / N := by
    have heq :
        2 * (J / N) - 1 / N = (2 * J - 1) / N := by
      field_simp [hN.ne']

    rw [heq]
    exact div_pos hstep hN
  have hright : 0 < 2 * (J / N) + 1 / N := by
    have heq :
        2 * (J / N) + 1 / N = (2 * J + 1) / N := by
      field_simp [hN.ne']

    rw [heq]
    exact div_pos (by linarith) hN
  have hroot :
      Real.sqrt
        ((2 * (J / N) - 1 / N) *
          (2 * (J / N) + 1 / N)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hleft hright)).ne'
  unfold normalizedNu
  rw [hrad, hdenrad,
    Real.sqrt_mul (sq_nonneg (N ^ 3)),
    Real.sqrt_sq (by positivity : 0 ≤ N ^ 3),
    Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
  field_simp [hN.ne', hJ.ne', hroot]
end MetricCodes.Johnson.SpectralAsymptotics
