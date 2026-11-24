-- Prove2me | solution 1 for GlobalTheory.twoSided_shift_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:20.511953+00:00
-- url     : https://prove2.me/submissions/e4fb2196-9e43-454d-8442-5f7197a4f21c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwoSidedShiftSeriesHasSum
import Theorems.Thm_GlobalTheory_TwoSidedShift_exists_sum_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) :=
  GlobalTheory.TwoSidedShift.exists_sum_shift
end GlobalTheory
