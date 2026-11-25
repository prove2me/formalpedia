-- Prove2me | solution 1 for GroundTheory.Automorphic.L2Kernel.kernelOp_apply_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:55:20.790873+00:00
-- url     : https://prove2.me/submissions/2964357e-d112-4f60-b10d-6656f14dc9a6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel

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
theorem _root_.solution (f : Lp 𝕜 2 ν) :
    kernelOp k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  kernelOpₗ_apply_ae k f
end GroundTheory.Automorphic.L2Kernel
