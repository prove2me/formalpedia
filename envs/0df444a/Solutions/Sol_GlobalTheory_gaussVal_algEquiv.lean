-- Prove2me | solution 1 for GlobalTheory.gaussVal_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:04:05.316109+00:00
-- url     : https://prove2.me/submissions/4a944bc8-b4ae-4f6f-aeb4-827f1cba371e

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

theorem solution (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (h : ∀ i, gaussVal v (e (X i)) ≤ 1) (h' : ∀ j, gaussVal v (e.symm (X j)) ≤ 1)
    (f : MvPolynomial σ R) : gaussVal v (e f) = gaussVal v f := by
  refine le_antisymm ?_ ?_
  · have he : e f = aeval (e ∘ X) f :=
      congrArg (fun φ => φ f) (aeval_unique e.toAlgHom)
    rw [he]
    exact gaussVal_aeval_le v (e ∘ X) h f
  · have he : e.symm (e f) = aeval (e.symm ∘ X) (e f) :=
      congrArg (fun φ => φ (e f)) (aeval_unique e.symm.toAlgHom)
    have hf : f = aeval (e.symm ∘ X) (e f) := by
      rw [← he, AlgEquiv.symm_apply_apply]
    nth_rw 1 [hf]
    exact gaussVal_aeval_le v (e.symm ∘ X) h' (e f)
