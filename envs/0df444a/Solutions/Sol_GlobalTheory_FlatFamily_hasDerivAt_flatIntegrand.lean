-- Prove2me | solution 1 for GlobalTheory.FlatFamily.hasDerivAt_flatIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:53.473354+00:00
-- url     : https://prove2.me/submissions/6cd80c71-e5fb-4076-9c70-b61bc2124c4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFamilyZetaConvergenceHolomorphy

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
theorem _root_.solution (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s : ℂ) (x : X) :
    HasDerivAt (fun z => flatIntegrand f a s₀ z x)
      (flatIntegrand f a s₀ s x * ((Real.log (a x) : ℝ) : ℂ)) s := by
  have h : ((a x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha x).ne'
  have h1 := (((hasDerivAt_id s).sub_const s₀).const_cpow (c := ((a x : ℝ) : ℂ))
    (Or.inl h)).const_mul (f x)
  simp only [flatIntegrand]
  refine h1.congr_deriv ?_
  rw [Complex.ofReal_log (ha x).le]
  simp only [id, mul_one]
  ring
end GlobalTheory.FlatFamily
