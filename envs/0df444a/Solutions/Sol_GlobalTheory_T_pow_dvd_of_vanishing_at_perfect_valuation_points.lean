-- Prove2me | solution 1 for GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:06.553535+00:00
-- url     : https://prove2.me/submissions/52ed116d-07be-4ba5-92b5-a847464eeacf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPointsStatement
import Theorems.Thm_GlobalTheory_s_points_kpt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) → ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by
  first | exact @GlobalTheory.s_points_kpt | exact GlobalTheory.s_points_kpt | (intros; apply GlobalTheory.s_points_kpt <;> assumption)
end _root_.GlobalTheory.T
