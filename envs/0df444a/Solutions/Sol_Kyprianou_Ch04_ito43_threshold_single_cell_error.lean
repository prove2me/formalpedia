-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_threshold_single_cell_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:59:59.893124+00:00
-- url     : https://prove2.me/submissions/bb0b7cb1-626b-490e-a1cc-b523a439848e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_half_square_difference_bound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution (X : NNReal → ℝ) (a d b t T : NNReal) (had : a ≤ d) (ht : t ≤ T)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hX : ∀ s ≤ T, |X s| ≤ R)
    (hp : b ≤ t → a < b → b < d → |X (min t d)-X b| ≤ δ) :
    |(X (min t d)-X (min t a))^2/2 -
       (X (min (min t b) d)-X (min (min t b) a))^2/2 -
       (if b ≤ a then (1:ℝ) else 0)*(X (min t d)-X (min t a))^2/2|
      ≤ if a < b ∧ b < d then 2*R*δ else 0 := by
  by_cases hb : b ≤ a
  · have hb' := hb.trans had
    have h1 : min (min t b) d = min t b := min_eq_left ((min_le_right _ _).trans hb')
    have h2 : min (min t b) a = min t b := min_eq_left ((min_le_right _ _).trans hb)
    simp [if_pos hb,h1,h2,not_lt.mpr hb]
  · have hab : a < b := lt_of_not_ge hb
    by_cases hd : d ≤ b
    · have h1 : min (min t b) d = min t d := by rw [min_assoc,min_eq_right hd]
      have h2 : min (min t b) a = min t a := by rw [min_assoc,min_eq_right hab.le]
      simp [if_neg hb,h1,h2,not_lt.mpr hd]
    · have hbd : b < d := lt_of_not_ge hd
      rw [if_neg hb,if_pos ⟨hab,hbd⟩]
      simp only [zero_mul,zero_div,sub_zero]
      by_cases htb : t ≤ b
      · rw [min_eq_left htb,sub_self,abs_zero]
        positivity
      · have hbt : b ≤ t := (lt_of_not_ge htb).le
        have hat := hab.le.trans hbt
        rw [min_eq_right hbt,min_eq_left hbd.le,min_eq_right hab.le,min_eq_right hat]
        exact ito43_half_square_difference_bound _ _ _ R δ hδ
          (hX _ ((min_le_left _ _).trans ht))
          (hX a (hat.trans ht)) (hX b (hbt.trans ht))
          (hp hbt hab hbd)
