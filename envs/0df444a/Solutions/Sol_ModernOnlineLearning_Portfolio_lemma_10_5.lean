-- Prove2me | solution 1 for ModernOnlineLearning.Portfolio.lemma_10_5
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T04:11:25.474969+00:00
-- url     : https://prove2.me/submissions/4db1dfd7-ba3e-458d-84a4-600b5252c707

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
set_option autoImplicit false

theorem solution {T : ℕ} (hT : 1 ≤ T) (a b : Fin T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t) :
    ENNReal.ofReal (∑ t, a t) / ENNReal.ofReal (∑ t, b t) ≤
      ⨆ t : Fin T, ENNReal.ofReal (a t) / ENNReal.ofReal (b t) := by
  classical
  let M : ENNReal := ⨆ t : Fin T, ENNReal.ofReal (a t) / ENNReal.ofReal (b t)
  change ENNReal.ofReal (∑ t, a t) / ENNReal.ofReal (∑ t, b t) ≤ M
  by_cases hM : M = ⊤
  · rw [hM]; exact le_top
  apply (ENNReal.div_le_iff_le_mul (Or.inr hM) (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ha i),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact (ENNReal.div_le_iff_le_mul (Or.inr hM) (Or.inl ENNReal.ofReal_ne_top)).mp (le_iSup (fun t : Fin T => ENNReal.ofReal (a t) / ENNReal.ofReal (b t)) t)


