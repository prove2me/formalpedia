-- Prove2me | solution 1 for GlobalTheory.FlatFamily.aestronglyMeasurable_flatIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:52.766443+00:00
-- url     : https://prove2.me/submissions/1b918035-8d2e-4417-b331-9210fff831f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFamilyZetaConvergenceHolomorphy
import Theorems.Thm_GlobalTheory_FlatFamily_flatIntegrand_rebase

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
namespace GlobalTheory.FlatFamily
theorem _root_.solution {μ : Measure X} {f : X → ℂ} {a : X → ℝ}
    (hm : Measurable a) (ha : ∀ x, 0 < a x) {s₀ s₁ : ℂ}
    (h : AEStronglyMeasurable (flatIntegrand f a s₀ s₁) μ) (s : ℂ) :
    AEStronglyMeasurable (flatIntegrand f a s₀ s) μ := by
  have e : flatIntegrand f a s₀ s
      = fun x => flatIntegrand f a s₀ s₁ x * ((a x : ℝ) : ℂ) ^ (s - s₁) :=
    funext (flatIntegrand_rebase f ha s₀ s₁ s)
  rw [e]
  refine h.mul ?_
  exact ((Complex.measurable_ofReal.comp hm).pow_const (s - s₁)).aestronglyMeasurable
end GlobalTheory.FlatFamily
