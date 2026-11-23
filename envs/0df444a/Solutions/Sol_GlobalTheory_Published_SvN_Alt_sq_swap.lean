-- Prove2me | solution 1 for GlobalTheory.Published.SvN.Alt.sq_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:17.44146+00:00
-- url     : https://prove2.me/submissions/68d9b081-6087-4eec-8e57-2d05251adbb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
namespace GlobalTheory.Published.SvN
namespace Alt
theorem _root_.solution (h : Alt c) {x y : W} (hxy : c x y ^ 2 = 1) : c y x ^ 2 = 1 := by
  have := congrArg (· ^ 2) (h.anti x y)
  simpa [mul_pow, hxy] using this
end Alt
end GlobalTheory.Published.SvN
