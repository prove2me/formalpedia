-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.range_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:37.710815+00:00
-- url     : https://prove2.me/submissions/37ad725a-9c5c-4432-814f-5c94f8abd680

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommNil
theorem _root_.solution (a : Module.End ℂ V) (i : ℕ) :
    LinearMap.range (a ^ (i + 1)) ≤ LinearMap.range (a ^ i) := by
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _
end GlobalTheory.CompanionTheory.CommNil
