-- Prove2me | solution 1 for GreenTao.linear_forms_cs_moments
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T21:34:44.575264+00:00
-- url     : https://prove2.me/submissions/4da76fbc-48c7-4ead-9315-8a524ef25075

import Theorems.Thm_GreenTao_linear_forms_cs_factor
import Theorems.Thm_GreenTao_linear_forms_cs_weight_moments
import Theorems.Thm_GreenTao_linear_forms_cube_average
import Mathlib

open scoped BigOperators Topology
open Filter GreenTao

theorem solution
    (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (μ : GreenTao.Family M) (hμ : ∀ n x, 0 ≤ μ n x)
    (hLF : GreenTao.LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) :
    Tendsto (fun n => GreenTao.csFactor d j (μ n)) atTop (𝓝 1) ∧
      ∀ q : ℕ, q ≤ 2 →
        Tendsto (fun n => GreenTao.avg fun x =>
          GreenTao.avg fun h : Fin d → ZMod (M n : ℕ) =>
            GreenTao.csWeight d j (μ n) x h ^ q *
              ∏ ω : Fin d → Bool, μ n (x + ∑ i : Fin d, if ω i then h i else 0))
          atTop (𝓝 1) := by
  refine ⟨linear_forms_cs_factor d hd M μ hLF j, ?_⟩
  intro q hq
  by_cases hq₀ : q = 0
  · subst q
    have h := linear_forms_cube_average M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1) d hLF
      (Nat.le_mul_of_pos_left _ (by omega)) (by omega) (by omega)
    simpa only [cubeAvg, pow_zero, one_mul] using h
  · exact linear_forms_cs_weight_moments d hd M μ hLF j q (by omega) hq
