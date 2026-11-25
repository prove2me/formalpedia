-- Prove2me | solution 1 for GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:02.767808+00:00
-- url     : https://prove2.me/submissions/d6459722-a5d9-4459-b194-eccbbc730623

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyLocalStatement
import Theorems.Thm_GlobalTheory_ConjLocal_conj_of_charpoly_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R), Y.charpoly = Y'.charpoly → Y.charpoly.Separable → ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by
  first | exact @GlobalTheory.ConjLocal.conj_of_charpoly_local | exact GlobalTheory.ConjLocal.conj_of_charpoly_local | (intros; apply GlobalTheory.ConjLocal.conj_of_charpoly_local <;> assumption)
end _root_.GlobalTheory.T
