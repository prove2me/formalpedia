-- Prove2me | solution 1 for GlobalTheory.T.twoSided_shift_series_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:29.184728+00:00
-- url     : https://prove2.me/submissions/b071a421-9191-4365-bcd1-17d810f8e600

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwoSidedShiftSeriesHasSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwoSidedShiftSeriesHasSumStatement
import Theorems.Thm_GlobalTheory_twoSided_shift_series


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  first | exact @GlobalTheory.twoSided_shift_series | exact GlobalTheory.twoSided_shift_series | (intros; apply GlobalTheory.twoSided_shift_series <;> assumption)
end _root_.GlobalTheory.T
