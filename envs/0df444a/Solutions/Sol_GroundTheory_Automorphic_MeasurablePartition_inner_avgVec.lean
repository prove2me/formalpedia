-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.inner_avgVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:13:43.492926+00:00
-- url     : https://prove2.me/submissions/e2c236e9-4eb3-4170-aa95-ab4ced8ec058

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace

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
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution (i : p.nonnull μ) (f : Lp ℂ 2 μ) :
    ⟪p.avgVec μ i, f⟫_ℂ = (((Real.sqrt (μ.real (p.E i)))⁻¹ : ℝ) : ℂ) * ∫ x in p.E i, f x ∂μ := by
  rw [avgVec, inner_smul_left, L2.inner_indicatorConstLp_one, Complex.conj_ofReal]
end GroundTheory.Automorphic.MeasurablePartition
