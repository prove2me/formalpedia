-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_contKernelOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:30.133272+00:00
-- url     : https://prove2.me/submissions/4c899b21-03ec-4a8a-b1ad-e51571d30c15

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_trace_contKernelOp_of_uniformSpace

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
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
namespace GroundTheory.Automorphic
theorem _root_.solution (k : C(X × X, ℂ)) (hT : IsTraceClass (contKernelOp μ k)) :
    trace (contKernelOp μ k) = ∫ x, k (x, x) ∂μ := by
  let _ : UniformSpace X := uniformSpaceOfCompactR1
  exact trace_contKernelOp_of_uniformSpace μ k hT
end GroundTheory.Automorphic
