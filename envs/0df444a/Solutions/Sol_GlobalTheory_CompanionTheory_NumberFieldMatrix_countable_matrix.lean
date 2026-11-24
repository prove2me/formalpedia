-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:41.06394+00:00
-- url     : https://prove2.me/submissions/a10057b7-86d6-453e-a735-1c8f25c143fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountableOfNumberField
import Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldMatrix_countable_of_numberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NumberFieldMatrix
namespace GlobalTheory.CompanionTheory.NumberFieldMatrix
theorem _root_.solution (E : Type) [Field E] [NumberField E] (m n : ℕ) :
    Countable (Matrix (Fin m) (Fin n) E) := by
  haveI := GlobalTheory.CompanionTheory.NumberFieldMatrix.countable_of_numberField E
  exact inferInstanceAs (Countable (Fin m → Fin n → E))
end GlobalTheory.CompanionTheory.NumberFieldMatrix
