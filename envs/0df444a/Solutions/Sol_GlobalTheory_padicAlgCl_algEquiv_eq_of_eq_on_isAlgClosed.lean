-- Prove2me | solution 1 for GlobalTheory.padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:43:04.116638+00:00
-- url     : https://prove2.me/submissions/b48b3b80-c113-4663-a04d-c86bb055171f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicAutomorphismUnique
import Theorems.Thm_GlobalTheory_denseRange_of_isAlgClosed_padicAlgCl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by
  intro l _ Ω _ _ j σ τ h
  have hc : ∀ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm (g : PadicAlgCl l →+* PadicAlgCl l)
      fun x => (spectralNorm_eq_of_equiv g x).symm).continuous
  have := (denseRange_of_isAlgClosed_padicAlgCl l Ω j).equalizer (hc σ) (hc τ) (funext h)
  exact AlgEquiv.ext fun x => congrFun this x
end GlobalTheory
