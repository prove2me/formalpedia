-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.tendsto_midpointCorrection_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/ab5cd224-3be2-4433-89c6-21d3f2da9cf1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_MidpointQuadrature_midpointCorrection_abs_lt_of_uniform_derivative

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Set
open scoped Topology BigOperators
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
namespace MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
theorem _root_.solution
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (g x) x) :
    Tendsto (midpointCorrection f) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, huniform⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) ε hε
  have hevent : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) < δ :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually
      (gt_mem_nhds hδ)
  obtain ⟨N₀, hN₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hpositive : 0 < N := by omega
  have hmesh : 1 / (N : ℝ) < δ := hN₀ N (by omega)
  rw [Real.dist_eq, sub_zero]
  exact midpointCorrection_abs_lt_of_uniform_derivative
    hf hderiv hε huniform hpositive hmesh
end MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
