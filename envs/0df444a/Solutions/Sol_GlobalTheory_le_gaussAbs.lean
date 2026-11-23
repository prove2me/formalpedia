-- Prove2me | solution 1 for GlobalTheory.le_gaussAbs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:24.6419+00:00
-- url     : https://prove2.me/submissions/309eaef1-4f39-4ed3-8a2b-b8bf57bbb55f

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
variable {R σ τ : Type*} [CommRing R]
variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
namespace GlobalTheory
theorem _root_.solution (f : MvPolynomial σ R) (m : σ →₀ ℕ) : a (coeff m f) ≤ gaussAbs a ha f :=
  NNReal.coe_le_coe.mpr (le_gaussVal (absValuation a ha) f m)
end GlobalTheory
