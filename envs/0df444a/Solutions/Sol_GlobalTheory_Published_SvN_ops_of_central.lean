-- Prove2me | solution 1 for GlobalTheory.Published.SvN.ops_of_central
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:33.577745+00:00
-- url     : https://prove2.me/submissions/b3246de9-1b35-4a5a-989f-8fa6a669ee91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_apply_eq

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
theorem _root_.solution (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) : Ops (fun x y => ψ (B x y / 2)) fun x => π ⟨x, 0⟩ where
  zero v := by rw [hπ]; simp
  mul x y v := by rw [← Module.End.mul_apply, ← map_mul, apply_eq hπ]; simp
end GlobalTheory.Published.SvN
