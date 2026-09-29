-- Prove2me | solution 1 for GeneralCK.Correction.Mdet_pos_iff_Kfactored_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:52:03.737716+00:00
-- url     : https://prove2.me/submissions/c0a7e9aa-00ce-4ab9-b9a1-967ec3a280e5

import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_entries
import Definitions.Def_GeneralCK_correction_minors
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_entropyInverse_spec

section
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h









end GeneralCK
end

section
namespace GeneralCK



theorem entropyInverse_pos {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    0 < entropyInverse h := by
  obtain ⟨hv, _, heq⟩ := entropyInverse_spec h0.le h1
  apply lt_of_le_of_ne hv
  intro he
  rw [← he, H_zero] at heq
  linarith











end GeneralCK
end

section
namespace GeneralCK
open Set Filter
open scoped Topology

theorem entropyInverse_lt_half {h : ℝ} (h0 : 0 ≤ h) (h1 : h < 1) :
    entropyInverse h < 1 / 2 := by
  obtain ⟨_, hv, heq⟩ := entropyInverse_spec h0 h1.le
  apply lt_of_le_of_ne hv
  intro hh
  rw [hh, H_half] at heq
  linarith







theorem J_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < J v := by
  apply div_pos _ log_two_pos
  apply Real.log_pos
  apply (lt_div_iff₀ hv).2
  linarith













end GeneralCK
end

section
namespace GeneralCK.Correction









theorem Mdet_rank_one (e f : ℝ) :
    Mdet e f = Aleft e f * Aright e f - (q e + q f)^2 -
      rankWeight e f * (Aleft e f * (Zright e f)^2 +
        Aright e f * (Zleft e f)^2 +
        2 * (q e + q f) * Zleft e f * Zright e f) := by
  unfold Mdet Mleft Mright Mcross rankWeight
  ring

theorem naturalJ_pos {f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < naturalJ f :=
  mul_pos log_two_pos (J_pos (entropyInverse_pos hf hf'.le)
    (entropyInverse_lt_half hf.le hf'))

theorem Aright_eq_numerator (e f : ℝ) :
    Aright e f = rightNumerator e f / naturalJ f := rfl

theorem naturalJ_mul_Aright {e f : ℝ} (hJ : naturalJ f ≠ 0) :
    naturalJ f * Aright e f = rightNumerator e f := by
  rw [Aright_eq_numerator]
  exact mul_div_cancel₀ _ hJ

/-- The nonzero slope hypothesis is essential when clearing the right denominator. -/
theorem Kfactored_eq_mul_Mdet {e f : ℝ} (hJ : naturalJ f ≠ 0) :
    Kfactored e f = naturalJ f * Mdet e f := by
  rw [Mdet_rank_one]
  unfold Kfactored
  linear_combination
    (rankWeight e f * (Zleft e f)^2 - Aleft e f) *
      (naturalJ_mul_Aright (e := e) hJ)

theorem Kfactored_eq_mul_Mdet_interior {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    Kfactored e f = naturalJ f * Mdet e f :=
  Kfactored_eq_mul_Mdet (naturalJ_pos hf hf').ne'





end GeneralCK.Correction
end

open GeneralCK GeneralCK.Correction

theorem solution {e f : ℝ} (hf : 0 < f) (hf' : f < 1) :
    0 < Mdet e f ↔ 0 < Kfactored e f := by
  rw [Kfactored_eq_mul_Mdet_interior hf hf']
  exact (mul_pos_iff_of_pos_left (naturalJ_pos hf hf')).symm
