-- Prove2me | solution 1 for GlobalTheory.exists_gaussAbs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:00:04.927799+00:00
-- url     : https://prove2.me/submissions/d41be62e-fe01-4597-98ac-6b4c29e011f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_exists_gaussVal_eq

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
theorem _root_.solution (f : MvPolynomial σ R) : ∃ m, gaussAbs a ha f = a (coeff m f) :=
  (exists_gaussVal_eq (absValuation a ha) f).imp fun _ h => by
    rw [gaussAbs_apply, h, coe_absValuation]
end GlobalTheory
