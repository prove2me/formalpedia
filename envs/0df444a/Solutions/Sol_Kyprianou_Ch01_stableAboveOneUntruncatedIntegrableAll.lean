-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneUntruncatedIntegrableAll
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:08:39.731641+00:00
-- url     : https://prove2.me/submissions/2bfb4f7e-0a50-44ca-993f-7d40e319a1ea

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAboveOneUntruncatedPositiveIntegrable
open MeasureTheory Set Real Complex
open scoped ComplexConjugate
set_option autoImplicit false
theorem solution
    (alpha xi : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (((xi * r : ℝ) : ℂ))) - 1 -
          Complex.I * (((xi * r : ℝ) : ℂ))) /
          (((r ^ (alpha + 1) : ℝ) : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
  by_cases hp : 0 < xi
  · exact Kyprianou.Ch01.stableAboveOneUntruncatedPositiveIntegrable
      alpha xi ha1 ha2 hp
  · by_cases hn : xi < 0
    · have hpos :=
        Kyprianou.Ch01.stableAboveOneUntruncatedPositiveIntegrable
          alpha (-xi) ha1 ha2 (neg_pos.mpr hn)
      have hconj : IntegrableOn
          (fun r : ℝ =>
            conj ((Complex.exp (Complex.I * (((-xi * r : ℝ) : ℂ))) - 1 -
              Complex.I * (((-xi * r : ℝ) : ℂ))) /
              (((r ^ (alpha + 1) : ℝ) : ℂ))))
          (Set.Ioi (0 : ℝ)) := by
        exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hpos
      apply (IntegrableOn.congr_fun hconj ?_ measurableSet_Ioi)
      intro r hr
      have hneg : (((xi * r : ℝ) : ℂ)) =
          -((((-xi) * r : ℝ) : ℂ)) := by push_cast; ring
      dsimp only
      rw [hneg]
      simp only [map_div₀, map_sub, map_mul, conj_ofReal,
        ← Complex.exp_conj, map_one, conj_I]
      congr 1
      all_goals ring
    · have hx : xi = 0 :=
        le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      subst xi
      simp
