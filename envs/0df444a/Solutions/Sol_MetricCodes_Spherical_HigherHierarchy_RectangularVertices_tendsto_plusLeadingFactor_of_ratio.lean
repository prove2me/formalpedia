-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_plusLeadingFactor_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/26a21a70-fc67-4f3d-8473-2a6882806a8f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_tendsto_wallShift_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_ambientShift_of_ratio

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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r : ℕ}
    (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1)) (ha : 0 ≤ a i)
    (hlim : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i + wallShift n r) /
          (2 * ambientShift n (lam n) i))
      atTop (𝓝 ((a i + 1) / (2 * a i + 1))) := by
  have hambient := tendsto_ambientShift_of_ratio lam a i hlim
  have hwall := tendsto_wallShift_div r
  have hden : 2 * (a i + (1 / 2 : ℝ)) ≠ 0 := by positivity
  have hlimit :=
    (hambient.add hwall).div (hambient.const_mul (2 : ℝ)) hden
  have hconverted :
      Tendsto
        (fun n : ℕ =>
          (ambientShift n (lam n) i / (n : ℝ) +
            wallShift n r / (n : ℝ)) /
            (2 * (ambientShift n (lam n) i / (n : ℝ))))
        atTop (𝓝 ((a i + 1) / (2 * a i + 1))) := by
    convert hlimit using 1
    · funext n
      rfl
    · congr 1
      ring
  apply hconverted.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn']
  <;> ring
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
