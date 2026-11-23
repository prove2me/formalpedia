-- Prove2me | solution 1 for GlobalTheory.Harm.mixedWeight_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:25.023005+00:00
-- url     : https://prove2.me/submissions/fb7db368-17e6-410e-a7fc-0e4cd07d1464

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
namespace GlobalTheory.Harm
theorem _root_.solution (m : ℕ) {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) (k : Fin m) :
    mixedWeight m a b k =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) -
        (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) := rfl
end GlobalTheory.Harm
