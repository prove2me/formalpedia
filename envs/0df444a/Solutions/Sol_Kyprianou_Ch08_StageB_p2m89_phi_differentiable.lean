-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_phi_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:36:43.09629+00:00
-- url     : https://prove2.me/submissions/d2a22928-1daa-4e5e-8588-c449b81b92b0

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_psi_differentiable_pos
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_continuous_pos
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful analytic reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ q : ℝ, 0 < q → DifferentiableAt ℝ (Phi ψ) q := by
  intro Ω mΩ P hP D ψ W hψ hW q hq
  have hzero : ψ 0 = 0 := by
    simpa [SpectrallyNegativeModel.toData] using (hψ 0 1 le_rfl (by norm_num)).2
  have hc := source_result81_law_laplace_convex Ω P D ψ hψ
  have hroot : Phi ψ q ∈ RightRootSet ψ q := (hW q hq.le).1.2.1
  have hv : ψ (Phi ψ q) = q := hroot.2
  have hr : 0 < Phi ψ q := by
    by_contra hn
    have hz : Phi ψ q = 0 := le_antisymm (le_of_not_gt hn) hroot.1
    rw [hz, hzero] at hv
    exact hq.ne hv
  have hdiff := p2m89_psi_differentiable_pos Ω P D ψ hψ (Phi ψ q) hr
  have hd := hdiff.hasDerivAt
  have hbound : q / Phi ψ q ≤ deriv ψ (Phi ψ q) := by
    have hs := hc.slope_le_of_hasDerivAt
      (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hr.le) hr hd
    simpa only [slope_def_field, hzero, hv, sub_zero] using hs
  have hdpos := (div_pos hq hr).trans_le hbound
  have hcont := p2m89_phi_continuous_pos ψ W hzero hc hW q hq
  have hfg : ∀ᶠ p in 𝓝 q, ψ (Phi ψ p) = p := by
    filter_upwards [Ioi_mem_nhds hq] with p hp
    have hp' : Phi ψ p ∈ RightRootSet ψ p := (hW p hp.le).1.2.1
    exact hp'.2
  exact (HasDerivAt.of_local_left_inverse hcont hd hdpos.ne' hfg).differentiableAt
