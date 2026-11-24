-- Prove2me | solution 1 for GlobalTheory.T.exists_presentation_square_at_point_of_localFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:34.398438+00:00
-- url     : https://prove2.me/submissions/438d87f6-4fc6-4c7d-8e5d-e9356a68327c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPresentationSquareAtPointOfLocalFactor
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPresentationSquareAtPointOfLocalFactorStatement
import Theorems.Thm_GlobalTheory_sqloc_present


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  first | exact @GlobalTheory.sqloc_present | exact GlobalTheory.sqloc_present | (intros; apply GlobalTheory.sqloc_present <;> assumption)
end _root_.GlobalTheory.T
