-- Prove2me | solution 1 for GeneralCK.noiseKernel_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T19:34:16.812027+00:00
-- url     : https://prove2.me/submissions/08dc965a-d5dc-481d-b55b-319333dacf1c

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

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
theorem solution {n : ℕ} (p : ℝ) (x : Cube n) :
    ∑ y, noiseKernel p x y = 1 := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
    (fun i b => if x i = b then 1 - p else p)
  have hb (i : Fin n) : (∑ b : Bool, if x i = b then 1 - p else p) = 1 := by
    cases x i <;> simp
  simpa only [noiseKernel, Fintype.piFinset_univ, hb, Finset.prod_const_one] using h.symm
