-- Prove2me | solution 1 for GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:17:29.29574+00:00
-- url     : https://prove2.me/submissions/9dcd6837-4a42-4b38-be1f-7df090fa6693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOneStatement
import Theorems.Thm_GlobalTheory_Nef_exists_unique_place_ord_eq_one


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
theorem _root_.solution : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  first | exact @GlobalTheory.Nef.exists_unique_place_ord_eq_one | exact GlobalTheory.Nef.exists_unique_place_ord_eq_one | (intros; apply GlobalTheory.Nef.exists_unique_place_ord_eq_one <;> assumption)
end _root_.GlobalTheory.T
