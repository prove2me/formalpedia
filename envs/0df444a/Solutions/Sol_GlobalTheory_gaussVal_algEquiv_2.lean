-- Prove2me | solution 2 for GlobalTheory.gaussVal_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:19.436155+00:00
-- url     : https://prove2.me/submissions/efcf3f5c-6fe3-484d-90f8-7cbe2233caa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_gaussVal_algHom_le

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
theorem _root_.solution (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (h : ∀ i, gaussVal v (e (X i)) ≤ 1) (h' : ∀ j, gaussVal v (e.symm (X j)) ≤ 1)
    (f : MvPolynomial σ R) : gaussVal v (e f) = gaussVal v f := by
  refine le_antisymm (gaussVal_algHom_le v e.toAlgHom h f) ?_
  simpa using gaussVal_algHom_le v e.symm.toAlgHom h' (e f)
end GlobalTheory
