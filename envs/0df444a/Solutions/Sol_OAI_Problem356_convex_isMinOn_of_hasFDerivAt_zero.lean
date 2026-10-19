-- Prove2me | solution 1 for OAI.Problem356.convex_isMinOn_of_hasFDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:59:50.488413+00:00
-- url     : https://prove2.me/submissions/a7c600ef-d1c9-4a74-89ad-6e594be9d110

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity

open OAI OAI.Problem356
universe uE uP
open Set Filter
open scoped Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem pb_convex_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := by
  intro y hy
  show f x ≤ f y
  by_contra hlt
  push Not at hlt
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφ
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd' : HasFDerivAt f (0 : E →L[ℝ] ℝ) (x + (0 : ℝ) • (y - x)) := by simpa using hd
  have hφd : HasDerivAt φ 0 0 := by
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    rw [ContinuousLinearMap.zero_apply] at this
    exact this
  have hsl := hasDerivAt_iff_tendsto_slope.mp hφd
  have hsl' : Tendsto (slope φ 0) (𝓝[>] 0) (𝓝 0) := hsl.mono_left (nhdsGT_le_nhdsNE 0)
  have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1, slope φ 0 t ≤ f y - f x := by
    intro t ht
    have hconv := hf.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
    have heq : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq] at hconv
    rw [slope_def_field]
    simp only [hφ, zero_smul, add_zero, sub_zero, smul_eq_mul] at hconv ⊢
    rw [div_le_iff₀ ht.1]
    nlinarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope φ 0 t ≤ f y - f x :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) hbound
  have := le_of_tendsto hsl' hev
  linarith

theorem solution {s : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := by
  exact pb_convex_min hf hx hd

