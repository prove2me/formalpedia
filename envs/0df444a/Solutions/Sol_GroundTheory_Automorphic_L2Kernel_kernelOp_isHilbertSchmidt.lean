-- Prove2me | solution 1 for GroundTheory.Automorphic.L2Kernel.kernelOp_isHilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:20.097434+00:00
-- url     : https://prove2.me/submissions/3aa13984-fda2-400f-89ff-211e954d78e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Theorems.Thm_GroundTheory_Automorphic_L2Kernel_hsNormSq_kernelOp_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.L2Kernel
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]
variable (k : Lp 𝕜 2 (μ.prod ν))
namespace GroundTheory.Automorphic.L2Kernel
theorem _root_.solution : IsHilbertSchmidt (kernelOp k) :=
  (hsNormSq_kernelOp_le k).trans_lt (ENNReal.pow_lt_top enorm_lt_top)
end GroundTheory.Automorphic.L2Kernel
