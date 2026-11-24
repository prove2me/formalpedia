-- Prove2me | solution 1 for GlobalTheory.valuation_eval_le_gaussVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:18.767053+00:00
-- url     : https://prove2.me/submissions/19f9fe44-18de-48f5-8485-0fd0c7b384d9

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
theorem _root_.solution (x : σ → R) (hx : ∀ i, v (x i) ≤ 1) (f : MvPolynomial σ R) :
    v (eval x f) ≤ gaussVal v f :=
  valuation_eval₂_le_gaussVal v v (RingHom.id R) (fun _ => le_rfl) x hx f
end GlobalTheory
