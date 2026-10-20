-- Prove2me | solution 1 for OAI.Cotype.quotientFactor_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:02:18.528742+00:00
-- url     : https://prove2.me/submissions/8ce290fc-cfc3-4852-b1ef-0dc7b2d2272e

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient

open OAI OAI.Cotype
open scoped BigOperators
variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50q_rep (j : H →L[ℝ] X) (x : H ⧸ j.ker) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : H, j.ker.mkQL z = x ∧ ‖z‖ < ‖x‖ + ε := by
  obtain ⟨z, hz, hz'⟩ := Submodule.Quotient.norm_mk_lt x hε
  exact ⟨z, hz, hz'⟩

theorem t_qnorm (j : H →L[ℝ] X) : ‖j.ker.liftQL j le_rfl‖ ≤ ‖j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hε' : 0 < ε / (‖j‖ + 1) := by positivity
  obtain ⟨z, rfl, hz⟩ := h50q_rep j x hε'
  have e : j.ker.liftQL j le_rfl (j.ker.mkQL z) = j z := rfl
  rw [e]
  calc ‖j z‖ ≤ ‖j‖ * ‖z‖ := j.le_opNorm z
    _ ≤ ‖j‖ * (‖j.ker.mkQL z‖ + ε / (‖j‖ + 1)) := mul_le_mul_of_nonneg_left hz.le (norm_nonneg _)
    _ < ‖j‖ * ‖j.ker.mkQL z‖ + ε := by
      rw [mul_add]
      have : ‖j‖ * (ε / (‖j‖ + 1)) < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg j]
      linarith

theorem t_qcomp (j : H →L[ℝ] X) (hj : IsCompactOperator j) :
    IsCompactOperator (j.ker.liftQL j le_rfl) := by
  refine ⟨closure (j '' Metric.ball 0 2), hj.isCompact_closure_image_ball 2,
    Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H ⧸ j.ker) one_pos) ?_⟩
  intro x hx
  apply subset_closure
  rw [mem_ball_zero_iff] at hx
  obtain ⟨z, rfl, hz⟩ := h50q_rep j x one_pos
  exact ⟨z, by rw [mem_ball_zero_iff]; linarith, rfl⟩

theorem solution (j : H →L[ℝ] X) : ‖quotientFactor j‖ ≤ ‖j‖ := by
  exact t_qnorm j

