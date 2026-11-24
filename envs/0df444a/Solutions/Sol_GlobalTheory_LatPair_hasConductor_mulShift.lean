-- Prove2me | solution 1 for GlobalTheory.LatPair.hasConductor_mulShift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:23.252332+00:00
-- url     : https://prove2.me/submissions/82db629a-6fb3-44d0-aa5f-33863e3158d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

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
open SplitWeil
namespace GlobalTheory.LatPair
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (u : 𝒪[k]ˣ) :
    HasConductor (ψ.mulShift ((u : 𝒪[k]) : k)) 1 := fun x => by
  have hv : ∀ w : 𝒪[k]ˣ, ∀ y : k, valuation k (((w : 𝒪[k]) : k) * y) ≤ valuation k y := fun w y => by
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 (w : 𝒪[k]).2)
  rw [← hψ x]
  refine ⟨fun h y hy => ?_, fun h y hy => h _ ((hv u y).trans hy)⟩
  have := h _ ((hv u⁻¹ y).trans hy)
  rwa [AddChar.mulShift_apply, ← mul_assoc, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, one_mul] at this
end GlobalTheory.LatPair
