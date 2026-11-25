-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.inner_avgVec_contKernelOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:35.963427+00:00
-- url     : https://prove2.me/submissions/c01fb9c7-1f20-45c0-8653-e6866f28bc14

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_contKernelOp_apply_ae
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_inner_avgVec
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_coeFn_avgVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution (k : C(X × X, ℂ)) (i : p.nonnull μ) :
    ⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ =
      (((μ.real (p.E i))⁻¹ : ℝ) : ℂ) * ∫ x in p.E i, ∫ y in p.E i, k (x, y) ∂μ ∂μ := by
  set r : ℂ := (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) with hr
  have h1 : contKernelOp μ k (p.avgVec μ i) =ᵐ[μ] fun x => r * ∫ y in p.E i, k (x, y) ∂μ := by
    filter_upwards [contKernelOp_apply_ae μ k (p.avgVec μ i)] with x hx
    rw [hx, ← integral_indicator (p.measurableSet i), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_avgVec μ p i] with y hy
    rw [hy]
    by_cases hyE : y ∈ p.E i
    · rw [Set.indicator_of_mem hyE, Set.indicator_of_mem hyE, hr, mul_one]
      ring
    · simp [Set.indicator_of_notMem hyE]
  rw [inner_avgVec, integral_congr_ae (ae_restrict_of_ae h1), integral_const_mul, ← mul_assoc]
  congr 1
  rw [hr, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt measureReal_nonneg]
end GroundTheory.Automorphic.MeasurablePartition
