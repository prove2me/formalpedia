-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_quadratic_residue_ratio_of_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/93b296d0-0266-450e-9c86-4e5e0766225e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_quadratic_residue_ratio_eq_normalized

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
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hd : Tendsto (fun k => v k / u k) atTop (𝓝 d))
    (x : ℝ) :
    Tendsto
      (fun k =>
        (x - quadraticCoordinate (v k)) /
          (x - quadraticCoordinate (u k)))
      atTop (𝓝 (d ^ 2)) := by
  have hinv : Tendsto (fun k => (u k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hnum : Tendsto
      (fun k => x * ((u k)⁻¹) ^ 2 - (v k / u k) ^ 2 -
        (v k / u k) * (u k)⁻¹)
      atTop (𝓝 (-d ^ 2)) := by
    convert ((tendsto_const_nhds.mul (hinv.pow 2)).sub
      (hd.pow 2)).sub (hd.mul hinv) using 1 <;> norm_num
  have hden : Tendsto
      (fun k => x * ((u k)⁻¹) ^ 2 - 1 - (u k)⁻¹)
      atTop (𝓝 (-1)) := by
    convert ((tendsto_const_nhds.mul (hinv.pow 2)).sub
      tendsto_const_nhds).sub hinv using 1 <;> norm_num
  have hlimit := hnum.div hden (by norm_num : (-1 : ℝ) ≠ 0)
  have hvalue : -d ^ 2 / (-1 : ℝ) = d ^ 2 := by ring
  rw [hvalue] at hlimit
  apply hlimit.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with k hk
  exact (quadratic_residue_ratio_eq_normalized x (u k) (v k) hk.ne').symm
end MetricCodes.Spherical.HigherHierarchy
