-- Prove2me | solution 1 for MasulloRH.finite_low_height_trace_zeros
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T03:09:13.451677+00:00
-- url     : https://prove2.me/submissions/e31161c2-fea9-4f70-bb67-52254e71fa16

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.ZetaZeros

set_option autoImplicit false
open MasulloRH Set Metric

theorem solution :
    {ρ : ZetaZerosInTraceStrip (1 / 2) | |ρ.val.im| ^ 2 < 36}.Finite := by
  let S : Set ℂ := Metric.closedBall 0 7 ∩ riemannZetaZeros
  have hScompact : IsCompact (Metric.closedBall (0 : ℂ) 7) := isCompact_closedBall _ _
  have hS : S.Finite := by
    dsimp [S]
    exact IsCompact.inter_riemannZetaZeros_finite hScompact
  apply Set.Finite.of_injOn
      (s := {ρ : ZetaZerosInTraceStrip (1 / 2) | |ρ.val.im| ^ 2 < 36})
      (f := fun ρ : ZetaZerosInTraceStrip (1 / 2) => ρ.val)
      (t := S)
  · intro ρ hρ
    have hre0 : 0 < ρ.val.re := ρ.property.2.1
    have hre1 : ρ.val.re < 1 := ρ.property.2.2.1
    have him : ρ.val.im ^ 2 < 36 := by
      change |ρ.val.im| ^ 2 < 36 at hρ
      simpa only [sq_abs] using hρ
    have hnormsq : ‖ρ.val‖ ^ 2 ≤ (7 : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_nonneg ρ.val.re]
    have hnorm : ‖ρ.val‖ ≤ (7 : ℝ) := by
      nlinarith [norm_nonneg ρ.val]
    change ρ.val ∈ Metric.closedBall (0 : ℂ) 7 ∩ riemannZetaZeros
    refine ⟨?_, ?_⟩
    · simpa [mem_closedBall_zero_iff] using hnorm
    · exact ρ.property.1
  · intro ρ hρ σ hσ hEq
    exact Subtype.ext hEq
  · exact hS
