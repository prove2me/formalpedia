-- Prove2me | solution 1 for GlobalTheory.gaussVal_algHom_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:00.911245+00:00
-- url     : https://prove2.me/submissions/efc9bdbf-c661-4b9c-b0d5-c11dced1007d

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
variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)
namespace GlobalTheory
theorem _root_.solution (e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (h : ∀ i, gaussVal v (e (X i)) ≤ 1) (f : MvPolynomial σ R) :
    gaussVal v (e f) ≤ gaussVal v f := by
  rw [aeval_unique e]
  exact gaussVal_aeval_le v _ h f
end GlobalTheory
