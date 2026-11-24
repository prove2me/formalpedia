-- Prove2me | solution 1 for GlobalTheory.abs_norm_eq_prod_embeddings_closeOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:07.025108+00:00
-- url     : https://prove2.me/submissions/2fb8254e-2fae-4e9e-b58c-680a36bef7c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqOneOfNormOneValuationSubOneSmall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] (x : E) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ x‖ := by
  have h : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ x := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
      (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    simp
  rw [← norm_prod, ← h, Complex.norm_ratCast]
end GlobalTheory
