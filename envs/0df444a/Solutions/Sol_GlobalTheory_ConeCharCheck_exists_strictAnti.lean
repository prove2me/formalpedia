-- Prove2me | solution 1 for GlobalTheory.ConeCharCheck.exists_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:38:19.374077+00:00
-- url     : https://prove2.me/submissions/35367d78-1467-4dc6-b9c3-6ce3567b4c19

import Mathlib
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_DegenerateExamples_ExistsStrictAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConeCharCheck
namespace GlobalTheory.ConeCharCheck
theorem _root_.solution (r : ℕ) : ∃ a : Fin r → ℤ, StrictAnti a :=
  ⟨fun i => -(i : ℤ), fun i j hij => by
    have : (i : ℕ) < j := hij
    simp only; omega⟩
end GlobalTheory.ConeCharCheck
