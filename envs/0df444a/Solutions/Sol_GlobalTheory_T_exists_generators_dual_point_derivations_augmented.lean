-- Prove2me | solution 1 for GlobalTheory.T.exists_generators_dual_point_derivations_augmented
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:51:05.592323+00:00
-- url     : https://prove2.me/submissions/a07dbf54-4202-4a5e-977d-73725773780e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGeneratorsDualPointDerivationsAugmented
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGeneratorsDualPointDerivationsAugmentedStatement
import Theorems.Thm_GlobalTheory_exists_generators_dual_point_derivations


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
theorem _root_.solution : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k), (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧ (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.exists_generators_dual_point_derivations | exact GlobalTheory.exists_generators_dual_point_derivations | (intros; apply GlobalTheory.exists_generators_dual_point_derivations <;> assumption)
end _root_.GlobalTheory.T
