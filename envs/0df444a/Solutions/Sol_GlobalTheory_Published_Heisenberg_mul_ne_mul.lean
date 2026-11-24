-- Prove2me | solution 1 for GlobalTheory.Published.Heisenberg.mul_ne_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:08.670178+00:00
-- url     : https://prove2.me/submissions/ba65d3aa-0b34-4a72-8722-06bbd94f11cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_Heisenberg_mul_eq_central_mul

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
theorem _root_.solution (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) {x y : W} (hxy : B x y ≠ 0) :
    (⟨x, 0⟩ : Heisenberg B) * ⟨y, 0⟩ ≠ ⟨y, 0⟩ * ⟨x, 0⟩ := by
  intro h
  rw [mul_eq_central_mul h2 hB, mul_eq_right] at h
  exact hxy (congrArg Heisenberg.cen h)
end GlobalTheory.Published.Heisenberg
