-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T12:18:36.634142+00:00
-- url     : https://prove2.me/submissions/c1b6c9b1-a94d-41e9-8370-ef014cad2123

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E001
import Definitions.Def_OAIQ106E002
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node40_check : node40 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4538959) entry_2_0) (Integer.Sparse.scale (-459927) entry_2_1) := by decide +kernel

theorem node40_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node40 x = (((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) := by
  rw [node40_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node41_check : node41 =
    Integer.Sparse.merge (Integer.Sparse.scale (113157) entry_2_3) (Integer.Sparse.scale (3208427) entry_2_4) := by decide +kernel

theorem node41_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x = (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x) := by
  rw [node41_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node42_check : node42 =
    Integer.Sparse.merge (Integer.Sparse.scale (7528052) entry_2_2) node41 := by decide +kernel

theorem node42_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node42 x = (((7528052 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x)) := by
  rw [node42_check, Integer.Sparse.eval_merge]
  rw [node41_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node43_check : node43 =
    Integer.Sparse.merge node40 node42 := by decide +kernel

theorem node43_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x = ((((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((7528052 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) := by
  rw [node43_check, Integer.Sparse.eval_merge]
  rw [node40_eval, node42_eval]

theorem node44_check : node44 =
    Integer.Sparse.merge (Integer.Sparse.scale (1798169) entry_2_5) (Integer.Sparse.scale (-1474042) entry_2_6) := by decide +kernel

theorem node44_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node44 x = (((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + ((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x) := by
  rw [node44_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node45_check : node45 =
    Integer.Sparse.merge (Integer.Sparse.scale (445414) entry_2_8) (Integer.Sparse.scale (-425014) entry_2_9) := by decide +kernel

theorem node45_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node45 x = (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + ((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x) := by
  rw [node45_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node46_check : node46 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1709009) entry_2_7) node45 := by decide +kernel

theorem node46_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node46 x = (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + ((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x)) := by
  rw [node46_check, Integer.Sparse.eval_merge]
  rw [node45_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node47_check : node47 =
    Integer.Sparse.merge node44 node46 := by decide +kernel

theorem node47_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node47 x = ((((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + ((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x) + (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + ((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x))) := by
  rw [node47_check, Integer.Sparse.eval_merge]
  rw [node44_eval, node46_eval]

theorem node48_check : node48 =
    Integer.Sparse.merge node43 node47 := by decide +kernel

theorem node48_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node48 x = (((((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((7528052 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) + ((((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + ((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x) + (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + ((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x)))) := by
  rw [node48_check, Integer.Sparse.eval_merge]
  rw [node43_eval, node47_eval]

theorem node49_check : node49 =
    Integer.Sparse.merge (Integer.Sparse.scale (581829) entry_2_10) (Integer.Sparse.scale (158367) entry_2_11) := by decide +kernel

theorem node49_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x = (((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x) := by
  rw [node49_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node50_check : node50 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1105957) entry_2_13) (Integer.Sparse.scale (1559599) entry_2_14) := by decide +kernel

theorem node50_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node50 x = (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + ((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x) := by
  rw [node50_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node51_check : node51 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2343572) entry_2_12) node50 := by decide +kernel

theorem node51_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x = (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + ((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x)) := by
  rw [node51_check, Integer.Sparse.eval_merge]
  rw [node50_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node52_check : node52 =
    Integer.Sparse.merge node49 node51 := by decide +kernel

theorem node52_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node52 x = ((((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x) + (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + ((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x))) := by
  rw [node52_check, Integer.Sparse.eval_merge]
  rw [node49_eval, node51_eval]

theorem node53_check : node53 =
    Integer.Sparse.merge (Integer.Sparse.scale (940149) entry_2_16) (Integer.Sparse.scale (2067282) entry_2_17) := by decide +kernel

theorem node53_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node53 x = (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) := by
  rw [node53_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node54_check : node54 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2556995) entry_2_15) node53 := by decide +kernel

theorem node54_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x = (((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x)) := by
  rw [node54_check, Integer.Sparse.eval_merge]
  rw [node53_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node55_check : node55 =
    Integer.Sparse.merge (Integer.Sparse.scale (-678125) entry_2_19) (Integer.Sparse.scale (2527166) entry_2_20) := by decide +kernel

theorem node55_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node55 x = (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + ((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x) := by
  rw [node55_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node56_check : node56 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1719750) entry_2_18) node55 := by decide +kernel

theorem node56_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node56 x = (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + ((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x)) := by
  rw [node56_check, Integer.Sparse.eval_merge]
  rw [node55_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node57_check : node57 =
    Integer.Sparse.merge node54 node56 := by decide +kernel

theorem node57_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node57 x = ((((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x)) + (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + ((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x))) := by
  rw [node57_check, Integer.Sparse.eval_merge]
  rw [node54_eval, node56_eval]

theorem node58_check : node58 =
    Integer.Sparse.merge node52 node57 := by decide +kernel

theorem node58_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node58 x = (((((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x) + (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + ((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x))) + ((((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x)) + (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + ((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x)))) := by
  rw [node58_check, Integer.Sparse.eval_merge]
  rw [node52_eval, node57_eval]

theorem node59_check : node59 =
    Integer.Sparse.merge node48 node58 := by decide +kernel

theorem node59_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x = ((((((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + ((-459927 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x) + (((7528052 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + ((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x))) + ((((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x + ((-1474042 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x) + (((-1709009 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + (((445414 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x + ((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x)))) + (((((581829 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x + ((158367 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x) + (((-2343572 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x + (((-1105957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + ((1559599 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x))) + ((((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x + (((940149 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2067282 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x)) + (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + (((-678125 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x + ((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x))))) := by
  rw [node59_check, Integer.Sparse.eval_merge]
  rw [node48_eval, node58_eval]

end MUB6.Certificate.GramAssembly.Block1

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

theorem sum_expand_21 {R : Type*} [AddCommMonoid R] (F : Fin 21 → R) :
    (∑ i, F i) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + F 6) + (F 7 + (F 8 + F 9)))) + (((F 10 + F 11) + (F 12 + (F 13 + F 14))) + ((F 15 + (F 16 + F 17)) + (F 18 + (F 19 + F 20))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + (F 12 + (F 13 + (F 14 + (F 15 + (F 16 + (F 17 + (F 18 + (F 19 + (F 20 + 0))))))))))))))))))))) = ((((F 0 + F 1) + (F 2 + (F 3 + F 4))) + ((F 5 + F 6) + (F 7 + (F 8 + F 9)))) + (((F 10 + F 11) + (F 12 + (F 13 + F 14))) + ((F 15 + (F 16 + F 17)) + (F 18 + (F 19 + F 20)))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

theorem row_eval_2_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x =
      ∑ j : Fin 21, (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x := by
  rw [node59_eval]
  exact (sum_expand_21 (fun j => (weights 2 j : ℝ) * Integer.Sparse.eval (entries 2 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_2_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_2_e_oai
