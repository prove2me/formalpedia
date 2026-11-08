-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:54.707547+00:00
-- url     : https://prove2.me/submissions/7d3e1dc4-fd36-41da-bd8a-3b8574078bd0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E178
import Definitions.Def_OAIQ106E196

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node336_check : node336 =
    Integer.Sparse.merge (Integer.Sparse.scale (4000099) entry_16_0) (Integer.Sparse.scale (-11676267) entry_16_1) := by decide +kernel

theorem node336_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node336 x = (((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) := by
  rw [node336_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node337_check : node337 =
    Integer.Sparse.merge (Integer.Sparse.scale (-146963) entry_16_3) (Integer.Sparse.scale (-8882925) entry_16_4) := by decide +kernel

theorem node337_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node337 x = (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x) := by
  rw [node337_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node338_check : node338 =
    Integer.Sparse.merge (Integer.Sparse.scale (-11528195) entry_16_2) node337 := by decide +kernel

theorem node338_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node338 x = (((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x)) := by
  rw [node338_check, Integer.Sparse.eval_merge]
  rw [node337_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node339_check : node339 =
    Integer.Sparse.merge node336 node338 := by decide +kernel

theorem node339_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node339 x = ((((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) + (((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x))) := by
  rw [node339_check, Integer.Sparse.eval_merge]
  rw [node336_eval, node338_eval]

theorem node340_check : node340 =
    Integer.Sparse.merge (Integer.Sparse.scale (-26700880) entry_16_6) (Integer.Sparse.scale (6927530) entry_16_7) := by decide +kernel

theorem node340_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node340 x = (((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + ((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x) := by
  rw [node340_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node341_check : node341 =
    Integer.Sparse.merge (Integer.Sparse.scale (6777335) entry_16_5) node340 := by decide +kernel

theorem node341_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node341 x = (((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + (((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + ((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x)) := by
  rw [node341_check, Integer.Sparse.eval_merge]
  rw [node340_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node342_check : node342 =
    Integer.Sparse.merge (Integer.Sparse.scale (8303639) entry_16_9) (Integer.Sparse.scale (-18516868) entry_16_10) := by decide +kernel

theorem node342_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node342 x = (((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x) := by
  rw [node342_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node343_check : node343 =
    Integer.Sparse.merge (Integer.Sparse.scale (-17209683) entry_16_8) node342 := by decide +kernel

theorem node343_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node343 x = (((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + (((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x)) := by
  rw [node343_check, Integer.Sparse.eval_merge]
  rw [node342_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node344_check : node344 =
    Integer.Sparse.merge node341 node343 := by decide +kernel

theorem node344_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node344 x = ((((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + (((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + ((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x)) + (((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + (((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x))) := by
  rw [node344_check, Integer.Sparse.eval_merge]
  rw [node341_eval, node343_eval]

theorem node345_check : node345 =
    Integer.Sparse.merge node339 node344 := by decide +kernel

theorem node345_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node345 x = (((((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) + (((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x))) + ((((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + (((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + ((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x)) + (((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + (((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x)))) := by
  rw [node345_check, Integer.Sparse.eval_merge]
  rw [node339_eval, node344_eval]

theorem node346_check : node346 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7480837) entry_16_11) (Integer.Sparse.scale (26441031) entry_16_12) := by decide +kernel

theorem node346_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node346 x = (((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x) := by
  rw [node346_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node347_check : node347 =
    Integer.Sparse.merge (Integer.Sparse.scale (-34667430) entry_16_14) (Integer.Sparse.scale (-40418461) entry_16_15) := by decide +kernel

theorem node347_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node347 x = (((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x) := by
  rw [node347_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node348_check : node348 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8763480) entry_16_13) node347 := by decide +kernel

theorem node348_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node348 x = (((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x)) := by
  rw [node348_check, Integer.Sparse.eval_merge]
  rw [node347_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node349_check : node349 =
    Integer.Sparse.merge node346 node348 := by decide +kernel

theorem node349_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node349 x = ((((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x) + (((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x))) := by
  rw [node349_check, Integer.Sparse.eval_merge]
  rw [node346_eval, node348_eval]

theorem node350_check : node350 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6575663) entry_16_17) (Integer.Sparse.scale (-6508672) entry_16_18) := by decide +kernel

theorem node350_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node350 x = (((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x + ((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x) := by
  rw [node350_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node351_check : node351 =
    Integer.Sparse.merge (Integer.Sparse.scale (62053757) entry_16_16) node350 := by decide +kernel

theorem node351_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node351 x = (((62053757 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + (((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x + ((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x)) := by
  rw [node351_check, Integer.Sparse.eval_merge]
  rw [node350_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node352_check : node352 =
    Integer.Sparse.merge (Integer.Sparse.scale (-15271475) entry_16_20) (Integer.Sparse.scale (-47014529) entry_16_21) := by decide +kernel

theorem node352_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node352 x = (((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + ((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x) := by
  rw [node352_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node353_check : node353 =
    Integer.Sparse.merge (Integer.Sparse.scale (-977591) entry_16_19) node352 := by decide +kernel

theorem node353_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node353 x = (((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + (((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + ((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x)) := by
  rw [node353_check, Integer.Sparse.eval_merge]
  rw [node352_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node354_check : node354 =
    Integer.Sparse.merge node351 node353 := by decide +kernel

theorem node354_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node354 x = ((((62053757 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + (((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x + ((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x)) + (((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + (((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + ((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x))) := by
  rw [node354_check, Integer.Sparse.eval_merge]
  rw [node351_eval, node353_eval]

theorem node355_check : node355 =
    Integer.Sparse.merge node349 node354 := by decide +kernel

theorem node355_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node355 x = (((((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x) + (((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x))) + ((((62053757 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + (((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x + ((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x)) + (((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + (((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + ((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x)))) := by
  rw [node355_check, Integer.Sparse.eval_merge]
  rw [node349_eval, node354_eval]

theorem node356_check : node356 =
    Integer.Sparse.merge node345 node355 := by decide +kernel

theorem node356_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node356 x = ((((((4000099 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_0 x + ((-11676267 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_1 x) + (((-11528195 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_2 x + (((-146963 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_3 x + ((-8882925 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_4 x))) + ((((6777335 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_5 x + (((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_6 x + ((6927530 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_7 x)) + (((-17209683 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_8 x + (((8303639 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_9 x + ((-18516868 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_10 x)))) + (((((-7480837 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_11 x + ((26441031 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_12 x) + (((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_13 x + (((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_14 x + ((-40418461 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_15 x))) + ((((62053757 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_16 x + (((-6575663 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_17 x + ((-6508672 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_18 x)) + (((-977591 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_19 x + (((-15271475 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_20 x + ((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_16_21 x))))) := by
  rw [node356_check, Integer.Sparse.eval_merge]
  rw [node345_eval, node355_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced finite sums for assembling the exact Gram certificate. -/

open scoped BigOperators

namespace MUB6.Certificate.GramAssembly

theorem sum_expand_22 {R : Type*} [AddCommMonoid R] (F : Fin 22 → R) :
    (∑ i, F i) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + (F 6 + F 7)) + (F 8 + (F 9 + F 10)))) + (((F 11 + F 12) + (F 13 + (F 14 + F 15))) + ((F 16 + (F 17 + F 18)) + (F 19 + (F 20 + F 21))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + (F 12 + (F 13 + (F 14 + (F 15 + (F 16 + (F 17 + (F 18 + (F 19 + (F 20 + (F 21 + 0)))))))))))))))))))))) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + (F 6 + F 7)) + (F 8 + (F 9 + F 10)))) + (((F 11 + F 12) + (F 13 + (F 14 + F 15))) + ((F 16 + (F 17 + F 18)) + (F 19 + (F 20 + F 21)))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

theorem row_eval_16_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node356 x =
      ∑ j : Fin 22, (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x := by
  rw [node356_eval]
  exact (sum_expand_22 (fun j => (weights 16 j : ℝ) * Integer.Sparse.eval (entries 16 j) x)).symm

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_16_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_16_e_oai
