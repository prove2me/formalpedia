-- Prove2me | solution 1 for GeneralCK.entropyInverse_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:51:24.157701+00:00
-- url     : https://prove2.me/submissions/b56a7074-ab01-41a2-9264-3f859732ff94

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

@[simp] theorem H_zero : H 0 = 0 := by simp [H]

@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h







theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK

open GeneralCK in
theorem solution {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ entropyInverse h ∧ entropyInverse h ≤ 1 / 2 ∧ H (entropyInverse h) = h := by
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    H_continuous.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show h ∈ Set.Icc (H 0) (H (1 / 2)) by
    simpa only [H_zero, H_half, Set.mem_Icc] using And.intro h0 h1)
  rw [← heq, entropyInverse_H_lower hv.1 hv.2]
  exact ⟨hv.1, hv.2, rfl⟩
