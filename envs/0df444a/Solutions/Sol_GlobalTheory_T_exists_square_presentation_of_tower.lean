-- Prove2me | solution 1 for GlobalTheory.T.exists_square_presentation_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:42.700979+00:00
-- url     : https://prove2.me/submissions/eb8f6e2e-57d0-4bb3-b812-31ceb3254909

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTowerStatement
import Theorems.Thm_GlobalTheory_SquareTower_tower


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
theorem _root_.solution : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.SquareTower.tower | exact GlobalTheory.SquareTower.tower | (intros; apply GlobalTheory.SquareTower.tower <;> assumption)
end _root_.GlobalTheory.T
