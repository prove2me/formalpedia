-- Prove2me | solution 1 for O3.abovePhaseCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:09.65982+00:00
-- url     : https://prove2.me/submissions/a474b9ae-5157-4914-877d-add11731a8d8

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {M : ℝ} (hM : M ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    M * (aboveStepWeight M t) ^ 2 /
        (2 * aboveAccumulatedWeight M t) =
      (t : ℝ) / (t + 1 : ℕ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have htsucc0 : (t + 1 : ℝ) ≠ 0 := by positivity
  unfold aboveStepWeight aboveAccumulatedWeight
  push_cast
  field_simp [hM, ht0, htsucc0]
end O3
