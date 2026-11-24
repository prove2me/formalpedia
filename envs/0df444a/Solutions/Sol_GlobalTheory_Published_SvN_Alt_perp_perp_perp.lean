-- Prove2me | solution 1 for GlobalTheory.Published.SvN.Alt.perp_perp_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:05.602643+00:00
-- url     : https://prove2.me/submissions/3d4cc662-7deb-422f-9dde-deb697a208f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Alt_sq_swap

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
theorem _root_.solution (h : Alt c) (T : Set W) (a : W) (ha : a ∈ h.perp (h.perp (h.perp T))) : a ∈ h.perp T :=
  fun t ht => ha t fun _ hx => h.sq_swap (hx t ht)
end Alt
end GlobalTheory.Published.SvN
