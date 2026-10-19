-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_spectralAtom_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/6ec6e119-5729-42fb-97b8-1a9ef8f7548f

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
theorem _root_.solution :
    Tendsto (fun t : ℝ => spectralAtom (t ^ 2) / t)
      (𝓝[>] 0) (nhds 1) := by
  let q : ℝ → ℝ := fun t =>
    Real.sqrt (1 + t ^ 2) / (1 + 2 * t ^ 2)
  have hq : Continuous q := by
    dsimp [q]
    apply Continuous.div₀
    · exact Real.continuous_sqrt.comp
        (continuous_const.add (continuous_id.pow 2))
    · exact continuous_const.add
        (continuous_const.mul (continuous_id.pow 2))
    · intro t
      positivity
  have htend : Tendsto q (𝓝[>] 0) (nhds 1) := by
    convert hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1;
      simp [q]
  have heq : (fun t : ℝ => spectralAtom (t ^ 2) / t) =ᶠ[𝓝[>] 0] q := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    unfold spectralAtom quadraticCoordinate q
    rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht]
    field_simp [ht.ne']
  exact htend.congr' heq.symm
end MetricCodes.Spherical.HigherHierarchy
