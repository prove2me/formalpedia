-- Prove2me | solution 1 for GroundTheory.Automorphic.L2Kernel.kernelOp_toLp_apply_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:27.935797+00:00
-- url     : https://prove2.me/submissions/faf31a10-796a-4f68-aad6-ee2a804a0b1b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Theorems.Thm_GroundTheory_Automorphic_L2Kernel_kernelOp_apply_ae

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
namespace GroundTheory.Automorphic.L2Kernel
theorem _root_.solution {k : X × Y → 𝕜} (hk : MemLp k 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelOp (hk.toLp k) f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν := by
  filter_upwards [kernelOp_apply_ae (hk.toLp k) f, Measure.ae_ae_of_ae_prod hk.coeFn_toLp] with x h1 h2
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  rw [hy]
end GroundTheory.Automorphic.L2Kernel
