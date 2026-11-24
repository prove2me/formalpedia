-- Prove2me | solution 1 for GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:55.71946+00:00
-- url     : https://prove2.me/submissions/7eecb394-2709-4ff8-811e-237ed5f0d04c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRoot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRootStatement
import Theorems.Thm_GlobalTheory_extend_alg_hom_adjoin_integral_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ → ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 → ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω, ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))), ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  first | exact @GlobalTheory.extend_alg_hom_adjoin_integral_root | exact GlobalTheory.extend_alg_hom_adjoin_integral_root | (intros; apply GlobalTheory.extend_alg_hom_adjoin_integral_root <;> assumption)
end _root_.GlobalTheory.T
