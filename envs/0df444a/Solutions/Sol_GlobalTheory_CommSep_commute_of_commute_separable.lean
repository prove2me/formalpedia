-- Prove2me | solution 1 for GlobalTheory.CommSep.commute_of_commute_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:48:36.63231+00:00
-- url     : https://prove2.me/submissions/5f6e8be3-4bdc-467a-bcfe-050ca67cfcf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Theorems.Thm_GlobalTheory_CommSep_commute_aeval_of_commute
import Theorems.Thm_GlobalTheory_CommSep_eq_aeval_of_commute_of_separable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.CommSep
namespace GlobalTheory.CommSep
theorem _root_.solution : ∀ (E : Type) [Field E] (r : ℕ)
    (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E,
    m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  intro E _ r A₀ hs m n hm hn
  obtain ⟨q, rfl⟩ := eq_aeval_of_commute_of_separable A₀ hs n hn
  exact (commute_aeval_of_commute (m := m) hm q).eq
end GlobalTheory.CommSep
