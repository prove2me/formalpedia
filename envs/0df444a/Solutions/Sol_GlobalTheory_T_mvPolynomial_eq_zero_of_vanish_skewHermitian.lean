-- Prove2me | solution 1 for GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:39.366448+00:00
-- url     : https://prove2.me/submissions/bda80293-4dbd-4ef3-adad-a30be75507f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitianStatement
import Theorems.Thm_GlobalTheory_SkewDense_eq_zero_of_vanish_skew


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → σ ≠ AlgHom.id F E → Module.finrank F E = 2 →
    ∀ {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ)), Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) J = J → J.det ≠ 0 →
    ∀ Q : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.SkewDense.eq_zero_of_vanish_skew | exact GlobalTheory.SkewDense.eq_zero_of_vanish_skew | (intros; apply GlobalTheory.SkewDense.eq_zero_of_vanish_skew <;> assumption)
end _root_.GlobalTheory.T
