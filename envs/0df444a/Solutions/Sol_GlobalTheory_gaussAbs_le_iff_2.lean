-- Prove2me | solution 2 for GlobalTheory.gaussAbs_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:51.416329+00:00
-- url     : https://prove2.me/submissions/8fef2d3b-1673-4fe9-8f7f-44420ed682a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_le_gaussAbs
import Theorems.Thm_GlobalTheory_exists_gaussAbs_eq

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
variable {R σ τ : Type*} [CommRing R]
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
namespace GlobalTheory
theorem _root_.solution {f : MvPolynomial σ R} {r : ℝ} :
    gaussAbs a ha f ≤ r ↔ ∀ m, a (coeff m f) ≤ r := by
  refine ⟨fun h m => (le_gaussAbs a ha f m).trans h, fun h => ?_⟩
  obtain ⟨m, hm⟩ := exists_gaussAbs_eq a ha f
  exact hm ▸ h m
end GlobalTheory
