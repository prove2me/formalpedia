-- Prove2me | solution 1 for GlobalTheory.VFComp.diffAt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:24.447701+00:00
-- url     : https://prove2.me/submissions/95e8dd35-7c06-4405-9c1b-92aec3663af9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}
namespace GlobalTheory.VFComp
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) {f : E d → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    {x : E d} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hf).1).differentiableAt (hU.mem_nhds hx)
end GlobalTheory.VFComp
