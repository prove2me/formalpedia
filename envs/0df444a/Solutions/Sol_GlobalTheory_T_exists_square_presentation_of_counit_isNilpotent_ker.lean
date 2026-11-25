-- Prove2me | solution 1 for GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:02.12791+00:00
-- url     : https://prove2.me/submissions/5a1596d9-a731-4d04-b420-c80c1e854ba3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquarePresentationOfCounitalComul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquarePresentationOfCounitalComulStatement
import Theorems.Thm_GlobalTheory_square_presentation_of_counital_comul


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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.square_presentation_of_counital_comul | exact GlobalTheory.square_presentation_of_counital_comul | (intros; apply GlobalTheory.square_presentation_of_counital_comul <;> assumption)
end _root_.GlobalTheory.T
