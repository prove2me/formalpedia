-- Prove2me | solution 1 for GlobalTheory.le_polyAddContent_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:18.455565+00:00
-- url     : https://prove2.me/submissions/c834a4d2-1e9e-41de-9d88-ea89bad976a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_polyContent_le_iff

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
open MvPolynomial Module
variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
namespace GlobalTheory
theorem _root_.solution {c : (σ →₀ ℕ) →₀ M} {γ : Γ} :
    γ ≤ polyAddContent v b c ↔ ∀ m, γ ≤ basisAddVal v b (c m) :=
  polyContent_le_iff (AddValuation.toValuation v) b
    (γ := Multiplicative.ofAdd (OrderDual.toDual γ))
end GlobalTheory
