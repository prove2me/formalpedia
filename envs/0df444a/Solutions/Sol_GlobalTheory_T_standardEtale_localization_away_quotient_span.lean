-- Prove2me | solution 1 for GlobalTheory.T.standardEtale_localization_away_quotient_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:04.525136+00:00
-- url     : https://prove2.me/submissions/fb1d4eb8-cf29-4387-9784-b9cc96f2d4b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
import Theorems.Thm_GlobalTheory_standardEtale_mvPolynomial_hypersurface


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∃ (f g : MvPolynomial (Option (Fin n)) A), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) ∧ (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : Option (Fin n) → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv none (MvPolynomial.map ψ f)) ≠ 0) ∧ Nonempty (B ≃ₐ[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  first | exact @GlobalTheory.standardEtale_mvPolynomial_hypersurface | exact GlobalTheory.standardEtale_mvPolynomial_hypersurface | (intros; apply GlobalTheory.standardEtale_mvPolynomial_hypersurface <;> assumption)
end _root_.GlobalTheory.T
