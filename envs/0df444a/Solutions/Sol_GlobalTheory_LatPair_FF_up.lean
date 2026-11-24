-- Prove2me | solution 1 for GlobalTheory.LatPair.FF_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:26.886258+00:00
-- url     : https://prove2.me/submissions/b7a306dc-39f7-4c7e-8919-c0b25a2f5e6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_cross_up_ofDual
import Theorems.Thm_GlobalTheory_LatPair_sum_withLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
variable (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
namespace GlobalTheory.LatPair
theorem _root_.solution [Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}] (x : {x : Red L // x ≠ 0}) :
    FF q χ φ (up L q x) = ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, χ (f.1 x.1) • φ (ofDual L f) := by
  simp only [FF_apply, up_ker, sum_withLat, cross_up_ofDual]
end GlobalTheory.LatPair
