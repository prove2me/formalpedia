-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_phi_continuous_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:38:26.9458+00:00
-- url     : https://prove2.me/submissions/01392e99-e372-4a30-8fc9-53313bbf1f50

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_convex_positive_secant_inverse_bound
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

/-- Obtain local continuity from the explicit inverse secant bound. -/
theorem solution :
    ∀ (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      ψ 0 = 0 →
      ConvexOn ℝ (Ici (0 : ℝ)) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 < q → ContinuousAt (Phi ψ) q := by
  intro ψ W hzero hc hW q hq
  have hroot (p : ℝ) (hp : 0 < p) : 0 < Phi ψ p ∧ ψ (Phi ψ p) = p := by
    have h : Phi ψ p ∈ RightRootSet ψ p := (hW p hp.le).1.2.1
    have hv : ψ (Phi ψ p) = p := h.2
    refine ⟨?_, hv⟩
    by_contra hn
    have hz : Phi ψ p = 0 := le_antisymm (le_of_not_gt hn) h.1
    rw [hz, hzero] at hv
    exact hp.ne hv
  obtain ⟨hr, hv⟩ := hroot q hq
  apply continuousAt_of_locally_lipschitz (r := q / 2) (by positivity) (Phi ψ q / q)
  intro p hpdist
  simp only [Real.dist_eq] at hpdist ⊢
  have hp : 0 < p := by linarith [(abs_lt.mp hpdist).1]
  obtain ⟨hs, hw⟩ := hroot p hp
  have hb := p2m89_convex_positive_secant_inverse_bound ψ hzero hc _ _ hs hr
  rw [hw, hv] at hb
  rw [div_mul_eq_mul_div, mul_comm (Phi ψ q)]
  exact (le_div_iff₀ hq).mpr hb
