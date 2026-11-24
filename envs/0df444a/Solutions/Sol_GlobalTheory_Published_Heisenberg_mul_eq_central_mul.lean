-- Prove2me | solution 1 for GlobalTheory.Published.Heisenberg.mul_eq_central_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:51.180967+00:00
-- url     : https://prove2.me/submissions/99d5d04a-fb04-47f9-991d-8d85035364b8

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
open GlobalTheory.Published.Heisenberg
variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
namespace GlobalTheory.Published.Heisenberg
theorem _root_.solution (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) (g h : Heisenberg B) :
    g * h = (⟨0, B g.vec h.vec⟩ : Heisenberg B) * (h * g) := by
  ext
  · simp [add_comm]
  · simp [← hB.neg_eq g.vec h.vec]; field_simp; ring
end GlobalTheory.Published.Heisenberg
