-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_scaleCoordinate_sq_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/848b2cb2-0aba-4622-b488-195d7f8b49cb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => scaleCoordinate (c ^ 2) u / u)
      atTop (𝓝 c) := by
  have hinv : Tendsto (fun u : ℝ => u⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hinside :
      Tendsto
        (fun u : ℝ => u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1))
        atTop (𝓝 (4 * c ^ 2)) := by
    convert (hinv.pow 2).add
      ((hinv.add tendsto_const_nhds).const_mul (4 * c ^ 2)) using 1 <;>
      norm_num
  have hroot : Real.sqrt (4 * c ^ 2) = 2 * c := by
    rw [show (4 : ℝ) * c ^ 2 = (2 * c) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hlimit :
      Tendsto
        (fun u : ℝ =>
          (Real.sqrt (u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1)) - u⁻¹) / 2)
        atTop (𝓝 c) := by
    convert (hinside.sqrt.sub hinv).div_const 2 using 1 <;>
      simp [hroot]
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hquadratic : 0 ≤ quadraticCoordinate u := by
    unfold quadraticCoordinate
    positivity
  have hrad : 0 ≤ 1 + 4 * c ^ 2 * quadraticCoordinate u := by positivity
  have hsmall :
      0 ≤ u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1) := by positivity
  have hsqrt :
      Real.sqrt (u⁻¹ ^ 2 + 4 * c ^ 2 * (u⁻¹ + 1)) =
        Real.sqrt (1 + 4 * c ^ 2 * quadraticCoordinate u) / u := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (div_nonneg (Real.sqrt_nonneg _) hu.le)).mp
    rw [Real.sq_sqrt hsmall, div_pow, Real.sq_sqrt hrad]
    unfold quadraticCoordinate
    field_simp [hu.ne']
  rw [hsqrt]
  unfold scaleCoordinate
  field_simp [hu.ne']
end MetricCodes.Spherical.HigherHierarchy
