-- Prove2me | solution 1 for GlobalTheory.LatPair.maps_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:51.679722+00:00
-- url     : https://prove2.me/submissions/cd3d4c03-745f-45da-8ef7-122c324cab3a

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
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
variable [DecidableEq n'] [Fintype n] [DecidableEq n]
namespace GlobalTheory.LatPair
theorem _root_.solution (g : GL n' k) (h : GL n k) : Maps (g • P) (h • Q) x ↔ Maps P Q ((h⁻¹ : GL n k).val * x * g.val) := by
  simp only [maps_iff_hasVal, Pair.smul_hasVal, ← mulVec_mulVec]
  refine ⟨fun H y a hy => H (g • y) a (by simpa using hy), fun H y a hy => ?_⟩
  have := H _ a hy
  rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
end GlobalTheory.LatPair
