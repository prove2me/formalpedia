-- Prove2me | solution 1 for GlobalTheory.T.exists_binary_form_eq_mul_prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:59.360331+00:00
-- url     : https://prove2.me/submissions/32bfa851-4f5a-4a85-aa9f-a25e82e86b8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplits
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplitsStatement
import Theorems.Thm_GlobalTheory_Nef_binary_form_splits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E) (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧ ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A), ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) = algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by
  first | exact @GlobalTheory.Nef.binary_form_splits | exact GlobalTheory.Nef.binary_form_splits | (intros; apply GlobalTheory.Nef.binary_form_splits <;> assumption)
end _root_.GlobalTheory.T
