-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.succ_mul_drop_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:26.467991+00:00
-- url     : https://prove2.me/submissions/1a7a9123-447a-4c7b-99a5-1cd4359bcad4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Theorems.Thm_GlobalTheory_CompanionTheory_CommNil_finrank_range_pow_convex

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
theorem _root_.solution [FiniteDimensional ℂ V] (a : Module.End ℂ V) (x : ℕ) :
    (x + 1) * finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
      (x + 1) * finrank ℂ (LinearMap.range (a ^ (x + 1))) +
        finrank ℂ (LinearMap.range (a ^ 0)) := by
  induction x with
  | zero => omega
  | succ x ih =>
    have conv : 2 * finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
        finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1 + 1))) :=
      finrank_range_pow_convex a x
    have hm := Nat.mul_le_mul_left (x + 1) conv
    nlinarith [ih, hm]
end GlobalTheory.CompanionTheory.CommNil
