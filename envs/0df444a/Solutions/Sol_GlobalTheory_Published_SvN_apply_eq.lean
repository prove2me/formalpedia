-- Prove2me | solution 1 for GlobalTheory.Published.SvN.apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.154174+00:00
-- url     : https://prove2.me/submissions/5bd611ab-8ca8-407a-b572-f25fbbd5f949

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
open Heisenberg
variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) (g : Heisenberg B) (v : M) : π g v = ψ g.cen • π ⟨g.vec, 0⟩ v := by
  rw [← hπ, ← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp
end GlobalTheory.Published.SvN
