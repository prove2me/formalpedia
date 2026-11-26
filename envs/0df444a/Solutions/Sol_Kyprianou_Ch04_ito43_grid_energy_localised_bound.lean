-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_energy_localised_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:52:16.522354+00:00
-- url     : https://prove2.me/submissions/9cb0f323-3933-49fa-ad63-d9b06c80739d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_cosine_energy_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_grid_energy_bound
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- On a bounded path, the stopped grid energy is controlled by full-grid cosine deficits. -/
theorem solution (X : NNReal → ℝ) (T R t : NNReal) (hR : 0 < R) (ht : t ≤ T)
    (n : ℕ) (hn : 0 < n)
    (hX : ∀ a b : NNReal, a ≤ T → b ≤ T → |X a - X b| ≤ (R : ℝ)) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n, (X (v (k+1)) - X (v k))^2) ≤
      (Real.pi^2 * (R : ℝ)^2 / 2) *
        (∑ k ∈ Finset.range n, (1-Real.cos ((X (u (k+1)) - X (u k))/(R : ℝ)))) +
          (R : ℝ)^2 := by
  intro u v
  have hu : Monotone u := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity : 0 ≤ T)) (by positivity)
  have hN : u n = T := by
    dsimp [u]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast hn.ne')
  have hb (k : ℕ) (hk : k < n) : |X (u (k+1)) - X (u k)| ≤ (R : ℝ) := by
    apply hX
    · rw [← hN]; exact hu (Nat.succ_le_of_lt hk)
    · rw [← hN]; exact hu hk.le
  have H := Kyprianou.Ch04.ito43_grid_cosine_energy_bound n
    (fun k => X (u (k+1)) - X (u k)) (R : ℝ) (by exact_mod_cast hR) hb
  exact (Kyprianou.Ch04.ito43_stopped_grid_energy_bound X u hu n t R
    (fun a b ha hb => hX a b (ha.trans ht) (hb.trans ht))).trans (add_le_add_left H _)
