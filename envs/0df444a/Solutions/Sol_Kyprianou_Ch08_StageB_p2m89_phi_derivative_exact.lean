-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_phi_derivative_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:19:17.80871+00:00
-- url     : https://prove2.me/submissions/25962c78-2e65-4efa-9f01-07afe3f0142e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_psi_differentiable_pos
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_phi_continuous_pos
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    0 < deriv ψ (Phi ψ q) ∧ deriv (Phi ψ) q = (deriv ψ (Phi ψ q))⁻¹ := by
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
  have hd := (p2m89_psi_differentiable_pos Ω P D ψ hψ (Phi ψ q) hr).hasDerivAt
  have hb : q / Phi ψ q ≤ deriv ψ (Phi ψ q) := by
    have hs := hc.slope_le_of_hasDerivAt
      (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hr.le) hr hd
    simpa only [slope_def_field, hzero, hv, sub_zero] using hs
  have hp := (div_pos hq hr).trans_le hb
  have hcont := p2m89_phi_continuous_pos ψ W hzero hc hW q hq
  have hfg : ∀ᶠ r in 𝓝 q, ψ (Phi ψ r) = r := by
    filter_upwards [Ioi_mem_nhds hq] with r hpos
    exact (hW r hpos.le).1.2.1.2
  exact ⟨hp, (HasDerivAt.of_local_left_inverse hcont hd hp.ne' hfg).deriv⟩
