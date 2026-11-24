-- Prove2me | solution 1 for GlobalTheory.Published.SvN.Ops.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:07.057051+00:00
-- url     : https://prove2.me/submissions/1dc40480-1fe3-49ef-a599-53819c1f5ad2

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
variable {ρ : W → Module.End ℂ M}
namespace GlobalTheory.Published.SvN
namespace Ops
theorem _root_.solution (h : Alt c) (hρ : Ops c ρ) {x : W} {v : M} (hv : ρ x v = 0) : v = 0 := by
  have := hρ.mul (-x) x v
  rw [hv, map_zero, neg_add_cancel, hρ.zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (h.ne _ _)
end Ops
end GlobalTheory.Published.SvN
