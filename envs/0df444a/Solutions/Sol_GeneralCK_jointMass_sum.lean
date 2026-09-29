-- Prove2me | solution 1 for GeneralCK.jointMass_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T19:34:51.247704+00:00
-- url     : https://prove2.me/submissions/3948485e-1aad-49c4-9de3-bb0b28b1e1b2

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_noiseKernel_sum

open scoped BigOperators

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators





























end GeneralCK

namespace GeneralCK
open scoped BigOperators









end GeneralCK

namespace GeneralCK.Information
open scoped BigOperators













































end GeneralCK.Information

open GeneralCK in
theorem solution {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ b, ∑ y, jointMass f p b y = 1 := by
  classical
  have hb (x y : Cube n) :
      (∑ b : Bool, if f x = b then noiseKernel p x y else 0) = noiseKernel p x y := by
    cases f x <;> simp
  simp only [jointMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; arg 2; ext y; rw [Finset.sum_comm]
  simp only [hb]
  rw [Finset.sum_comm]
  simp [noiseKernel_sum, Cube, zpow_neg, zpow_natCast]
