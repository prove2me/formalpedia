-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_contKernelOp_of_uniformSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:07.242343+00:00
-- url     : https://prove2.me/submissions/30772c22-585a-43a0-849c-1dfa41a24e2d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_orthonormal_avgVec
import Theorems.Thm_GroundTheory_Automorphic_tendsto_finePart_avgProj
import Theorems.Thm_GroundTheory_Automorphic_tendsto_sum_inner_avgVec
import Theorems.Thm_GroundTheory_Automorphic_norm_sub_finProj_le_norm
import Theorems.Thm_GroundTheory_Automorphic_tendsto_trace_comp
import Theorems.Thm_GroundTheory_Automorphic_trace_comp_finProj


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
variable {X : Type*} [UniformSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open MeasurablePartition
namespace GroundTheory.Automorphic
theorem _root_.solution [μ.WeaklyRegular] (k : C(X × X, ℂ))
    (hT : IsTraceClass (contKernelOp μ k)) : trace (contKernelOp μ k) = ∫ x, k (x, x) ∂μ := by
  have h1 := tendsto_trace_comp hT (fun V => (finePart V).avgProj μ)
    (fun V x => norm_sub_finProj_le_norm ((finePart V).orthonormal_avgVec μ) x)
    (tendsto_finePart_avgProj μ)
  have h2 := tendsto_sum_inner_avgVec μ k
  refine tendsto_nhds_unique h1 (h2.congr fun V => ?_)
  exact (trace_comp_finProj _ _).symm
end GroundTheory.Automorphic
