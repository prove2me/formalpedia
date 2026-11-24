-- Prove2me | solution 1 for GlobalTheory.FlatFamily.norm_flatIntegrand_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:17.949069+00:00
-- url     : https://prove2.me/submissions/a3a94858-a7cd-46eb-ba97-e5cda3081d07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFamilyZetaConvergenceHolomorphy
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlatZetaIntegral_norm_flatIntegrand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.FlatFamily
open GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
omit [MeasurableSpace X]
namespace GlobalTheory.FlatFamily
theorem _root_.solution (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (ha1 : ∀ x, a x ≤ 1)
    (s₀ : ℂ) {s₁ s : ℂ} (hs : s₁.re ≤ s.re) (x : X) :
    ‖flatIntegrand f a s₀ s x‖ ≤ ‖flatIntegrand f a s₀ s₁ x‖ := by
  rw [norm_flatIntegrand f s₀ s (ha x), norm_flatIntegrand f s₀ s₁ (ha x)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (ha x) (ha1 x) (by linarith)) (norm_nonneg _)
end GlobalTheory.FlatFamily
