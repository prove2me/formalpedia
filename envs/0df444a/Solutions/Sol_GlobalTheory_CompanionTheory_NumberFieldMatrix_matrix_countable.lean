-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NumberFieldMatrix.matrix_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:43.306444+00:00
-- url     : https://prove2.me/submissions/327af4b9-4fac-44a5-9664-4ce1d74215f4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CountableOfNumberField
import Theorems.Thm_GlobalTheory_CompanionTheory_NumberFieldMatrix_countable_matrix

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
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] (m n : ℕ),
      Countable (Matrix (Fin m) (Fin n) E) :=
  fun E _ _ m n => countable_matrix E m n
end GlobalTheory.CompanionTheory.NumberFieldMatrix
