-- Prove2me | solution 1 for GlobalTheory.PowerSeriesCoeffSum.coeff_X_mul_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:29.588969+00:00
-- url     : https://prove2.me/submissions/57972065-1c0d-4898-b2f9-ef786c560f94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
import Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_coeff_part

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesCoeffSum
open MvPowerSeries Finsupp
variable {O : Type} [CommRing O] {a : ℕ}
namespace GlobalTheory.PowerSeriesCoeffSum
theorem _root_.solution (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if (1 ≤ m i ∧ ∀ j < i, m j = 0) then coeff m f else 0 := by
  rw [X, coeff_monomial_mul, one_mul]
  by_cases h1 : 1 ≤ m i
  · have hle : single i 1 ≤ m := by
      intro k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simp [single_apply, Ne.symm hk]
    rw [if_pos hle, coeff_part, tsub_add_cancel_of_le hle]
    have : (∀ j < i, (m - single i 1 : Fin a →₀ ℕ) j = 0) ↔ (∀ j < i, m j = 0) := by
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      have : j ≠ i := ne_of_lt hj
      simp [single_apply, Ne.symm this]
    simp only [this, h1, true_and]
  · have hle : ¬ single i 1 ≤ m := by
      intro h; exact h1 (by simpa using h i)
    simp [hle, h1]
end GlobalTheory.PowerSeriesCoeffSum
