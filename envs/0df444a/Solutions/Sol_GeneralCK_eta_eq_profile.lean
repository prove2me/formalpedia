-- Prove2me | solution 1 for GeneralCK.eta_eq_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:52:42.906587+00:00
-- url     : https://prove2.me/submissions/7d10b447-7269-454f-bc20-b43a7840c862

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_entropyInverse_H_lower

open scoped BigOperators
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)



@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h









end GeneralCK

open GeneralCK in
theorem solution {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    eta h = (1 - 2 * entropyInverse h) * J (entropyInverse h) := by
  by_cases heq : h = 1
  · subst h
    have hv : entropyInverse 1 = 1 / 2 := by
      simpa only [H_half] using entropyInverse_H_lower (v := (1 / 2 : ℝ))
        (by norm_num) le_rfl
    simp [eta, hv]
  · simp [eta, heq]
