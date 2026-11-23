-- Prove2me | solution 1 for GlobalTheory.le_gaussAddVal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:12.124032+00:00
-- url     : https://prove2.me/submissions/1da9e2a0-ad33-4807-9312-dc70db218ed4

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
variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
namespace GlobalTheory
theorem _root_.solution {f : MvPolynomial σ R} {γ : Γ} :
    γ ≤ gaussAddVal v f ↔ ∀ m, γ ≤ v (coeff m f) :=
  gaussVal_le_iff (AddValuation.toValuation v) (γ := Multiplicative.ofAdd (OrderDual.toDual γ))
end GlobalTheory
