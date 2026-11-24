-- Prove2me | solution 1 for GlobalTheory.UnipotentInvariant.biInvariant_leadMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:02:57.268496+00:00
-- url     : https://prove2.me/submissions/fdff2e2a-2e7f-47f5-a273-cf54262a2533

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
import Theorems.Thm_GlobalTheory_UnipotentInvariant_leadMinor_transpose
import Theorems.Thm_GlobalTheory_UnipotentInvariant_leadMinor_rowAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
namespace GlobalTheory.UnipotentInvariant
theorem _root_.solution (i : Fin p) : BiInvariant (K := K) (leadMinor i) :=
  ⟨leadMinor_rowAdd i, fun a b hab t M => by
    rw [leadMinor_transpose, leadMinor_transpose, leadMinor_rowAdd i a b hab]⟩
end GlobalTheory.UnipotentInvariant
