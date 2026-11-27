-- Prove2me | solution 2 for GlobalTheory.eq_gaussValFrac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:53.351948+00:00
-- url     : https://prove2.me/submissions/0c219ca7-eed0-4114-b872-aec8c09fb514

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]
namespace GlobalTheory
theorem _root_.solution {w : Valuation F Γ₀}
    (h : ∀ f : MvPolynomial σ K, w (algebraMap _ F f) = gaussVal v f) :
    w = gaussValFrac v σ F := by
  ext x
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) x
  simp [h]
end GlobalTheory
