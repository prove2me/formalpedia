-- Prove2me | solution 1 for GlobalTheory.T.cubical_function_of_homomorphism
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:11.976534+00:00
-- url     : https://prove2.me/submissions/f9f3b937-2098-4f5e-845a-d7e5e2ced460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicalFunctionOfHomomorphism
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CubicalFunctionOfHomomorphismStatement
import Theorems.Thm_GlobalTheory_hom_eq_evenness_defect_of_cube


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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommGroup A] (h : X → A), (∀ a b, h (a + b) = h a * h b) → ∃ k : X → A, (∀ a a' b : X, k (a + a' + b) * k a * k a' * k b = k (a + a') * k (a + b) * k (a' + b)) ∧ ∀ a, k (-a) = h a * k a := by
  first | exact @GlobalTheory.hom_eq_evenness_defect_of_cube | exact GlobalTheory.hom_eq_evenness_defect_of_cube | (intros; apply GlobalTheory.hom_eq_evenness_defect_of_cube <;> assumption)
end _root_.GlobalTheory.T
