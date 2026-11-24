-- Prove2me | solution 1 for GlobalTheory.T.matrix_commute_of_commute_separable_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:20.648999+00:00
-- url     : https://prove2.me/submissions/a5170c88-1b83-49e8-a351-f26df1dfe297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpolyStatement
import Theorems.Thm_GlobalTheory_CommSep_commute_of_commute_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E, m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  first | exact @GlobalTheory.CommSep.commute_of_commute_separable | exact GlobalTheory.CommSep.commute_of_commute_separable | (intros; apply GlobalTheory.CommSep.commute_of_commute_separable <;> assumption)
end _root_.GlobalTheory.T
