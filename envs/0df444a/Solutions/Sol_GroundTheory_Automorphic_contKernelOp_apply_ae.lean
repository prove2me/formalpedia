-- Prove2me | solution 1 for GroundTheory.Automorphic.contKernelOp_apply_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:53.311703+00:00
-- url     : https://prove2.me/submissions/862e463f-2c71-4a83-b69b-d6bb80a0aa3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_L2Kernel_kernelOp_toLp_apply_ae


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
  [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]
namespace GroundTheory.Automorphic
theorem _root_.solution (k : C(X × X, ℂ)) (f : Lp ℂ 2 μ) :
    contKernelOp μ k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂μ :=
  L2Kernel.kernelOp_toLp_apply_ae (memLp_contKernel μ k) f
end GroundTheory.Automorphic
