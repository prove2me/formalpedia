-- Prove2me | solution 1 for GlobalTheory.derivation_extend_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:12.935923+00:00
-- url     : https://prove2.me/submissions/85c763ec-ff5f-4ba3-9361-19aee11005ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationExtendMvPolynomial
import Theorems.Thm_GlobalTheory_coeffDerivAddHom_monomial
import Theorems.Thm_GlobalTheory_coeffDerivAddHom_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]
end GlobalTheory
