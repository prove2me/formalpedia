-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_mrrwG_boundary_quadratic_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/d74499b3-49ee-4e64-8049-9b51182fec24

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_lowerEndpointRoot_pos
import Theorems.Thm_MetricCodes_MRRW_lowerEndpointWeight_pos
import Theorems.Thm_MetricCodes_MRRW_lowerEndpointWeight_lt_half

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ))
      (lowerEndpointDerivative δ) 0 := by
  have hquadratic :
      HasDerivAt
        (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ)
        (2 * δ) 0 := by
    simpa [id_eq] using
      (((hasDerivAt_id (0 : ℝ)).pow 2).add
        ((hasDerivAt_id (0 : ℝ)).const_mul (2 * δ))).add_const
          (2 * δ)
  have hradical :
      HasDerivAt
        (fun r : ℝ =>
          1 - (r ^ 2 + 2 * δ * r + 2 * δ))
        (-2 * δ) 0 := by
    simpa using hquadratic.const_sub (1 : ℝ)
  have hradicalzero :
      1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ) ≠ 0 := by
    have hpositive : 0 < 1 - 2 * δ := by linarith
    simpa using hpositive.ne'
  have hroot :
      HasDerivAt
        (fun r : ℝ =>
          Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)))
        ((-2 * δ) / (2 * lowerEndpointRoot δ)) 0 := by
    simpa [lowerEndpointRoot] using
      hradical.sqrt hradicalzero
  have hnumerator :
      HasDerivAt
        ((fun _ : ℝ => (1 : ℝ)) -
          (fun r : ℝ =>
            Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ))))
        (0 - ((-2 * δ) / (2 * lowerEndpointRoot δ))) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hroot
  have hprobability :
      HasDerivAt
        (fun r : ℝ =>
          (1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2)
        (δ / (2 * lowerEndpointRoot δ)) 0 := by
    change
      HasDerivAt
        (fun r : ℝ =>
          (((fun _ : ℝ => (1 : ℝ)) -
            (fun s : ℝ =>
              Real.sqrt (1 - (s ^ 2 + 2 * δ * s + 2 * δ)))) r) /
            (2 : ℝ))
        (δ / (2 * lowerEndpointRoot δ)) 0
    exact
      (hnumerator.div_const (2 : ℝ)).congr_deriv (by ring)
  have hweight := lowerEndpointWeight_pos hδ
  have hweightone :
      lowerEndpointWeight δ ≠ 1 := by
    have h := lowerEndpointWeight_lt_half hhalf
    linarith
  have hentropyfun :
      MetricCodes.binaryEntropy =
        (fun a : ℝ => Real.binEntropy a / Real.log 2) :=
    funext MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log
  have hbinary :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        (lowerEndpointWeight δ) := by
    rw [hentropyfun]
    exact
      (Real.hasDerivAt_binEntropy hweight.ne'
        hweightone).div_const (Real.log 2)
  have hbinaryzero :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        ((1 - Real.sqrt
          (1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ))) / 2) := by
    simpa [lowerEndpointWeight, lowerEndpointRoot] using hbinary
  change
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.binaryEntropy
          ((1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2))
      (lowerEndpointDerivative δ) 0
  have hcoeff :
      ((Real.log (1 - lowerEndpointWeight δ) -
        Real.log (lowerEndpointWeight δ)) / Real.log 2) *
          (δ / (2 * lowerEndpointRoot δ)) =
        lowerEndpointDerivative δ := by
    unfold lowerEndpointDerivative
    field_simp [(lowerEndpointRoot_pos hhalf).ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  exact (hbinaryzero.comp 0 hprobability).congr_deriv hcoeff
end MetricCodes.MRRW
