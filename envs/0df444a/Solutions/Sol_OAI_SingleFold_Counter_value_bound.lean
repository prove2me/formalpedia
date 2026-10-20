-- Prove2me | solution 1 for OAI.SingleFold.Counter.value_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:08:38.636382+00:00
-- url     : https://prove2.me/submissions/bc92b73f-ea28-41ae-97d0-d9d3e491d671

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]


omit [DecidableEq Q] in
theorem solution (M : Machine Q J) (d : J → ℕ) (t : ℕ) (j : J) : (run M d t).value j ≤ d j+t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : run M d (t+1) = next M (run M d t) := by
      unfold run; rw [Function.iterate_succ_apply']
    rw [e]; unfold next
    split
    · omega
    · rename_i jj p _
      simp only
      by_cases hj : j = jj
      · subst hj; simp; omega
      · simp [Function.update_of_ne hj]; omega
    · rename_i jj p0 pd _
      split
      · simp only; omega
      · simp only
        by_cases hj : j = jj
        · subst hj; simp; omega
        · simp [Function.update_of_ne hj]; omega

