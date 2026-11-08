-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:30.738317+00:00
-- url     : https://prove2.me/submissions/afcfdaac-fa35-4c06-83cf-7c17485a4b38

import Mathlib
import Lean.Elab.Tactic.Omega
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node100_check : node100 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1637779) entry_5_0) (Integer.Sparse.scale (-104535) entry_5_1) := by decide +kernel

theorem node100_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node100 x = (((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) := by
  rw [node100_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node101_check : node101 =
    Integer.Sparse.merge (Integer.Sparse.scale (94961) entry_5_3) (Integer.Sparse.scale (792287) entry_5_4) := by decide +kernel

theorem node101_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node101 x = (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x) := by
  rw [node101_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node102_check : node102 =
    Integer.Sparse.merge (Integer.Sparse.scale (1798169) entry_5_2) node101 := by decide +kernel

theorem node102_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node102 x = (((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x)) := by
  rw [node102_check, Integer.Sparse.eval_merge]
  rw [node101_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node103_check : node103 =
    Integer.Sparse.merge node100 node102 := by decide +kernel

theorem node103_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x = ((((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) := by
  rw [node103_check, Integer.Sparse.eval_merge]
  rw [node100_eval, node102_eval]

theorem node104_check : node104 =
    Integer.Sparse.merge (Integer.Sparse.scale (4872019) entry_5_5) (Integer.Sparse.scale (-2061591) entry_5_6) := by decide +kernel

theorem node104_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x = (((4872019 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + ((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x) := by
  rw [node104_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node105_check : node105 =
    Integer.Sparse.merge (Integer.Sparse.scale (-125916) entry_5_8) (Integer.Sparse.scale (-3017686) entry_5_9) := by decide +kernel

theorem node105_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node105 x = (((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + ((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x) := by
  rw [node105_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node106_check : node106 =
    Integer.Sparse.merge (Integer.Sparse.scale (173690) entry_5_7) node105 := by decide +kernel

theorem node106_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node106 x = (((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + (((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + ((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x)) := by
  rw [node106_check, Integer.Sparse.eval_merge]
  rw [node105_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node107_check : node107 =
    Integer.Sparse.merge node104 node106 := by decide +kernel

theorem node107_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node107 x = ((((4872019 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + ((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x) + (((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + (((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + ((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x))) := by
  rw [node107_check, Integer.Sparse.eval_merge]
  rw [node104_eval, node106_eval]

theorem node108_check : node108 =
    Integer.Sparse.merge node103 node107 := by decide +kernel

theorem node108_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node108 x = (((((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) + ((((4872019 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + ((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x) + (((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + (((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + ((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x)))) := by
  rw [node108_check, Integer.Sparse.eval_merge]
  rw [node103_eval, node107_eval]

theorem node109_check : node109 =
    Integer.Sparse.merge (Integer.Sparse.scale (991536) entry_5_10) (Integer.Sparse.scale (1695692) entry_5_11) := by decide +kernel

theorem node109_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x = (((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x) := by
  rw [node109_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node110_check : node110 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2053220) entry_5_13) (Integer.Sparse.scale (2143288) entry_5_14) := by decide +kernel

theorem node110_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node110 x = (((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + ((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x) := by
  rw [node110_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node111_check : node111 =
    Integer.Sparse.merge (Integer.Sparse.scale (1212441) entry_5_12) node110 := by decide +kernel

theorem node111_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node111 x = (((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x + (((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + ((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x)) := by
  rw [node111_check, Integer.Sparse.eval_merge]
  rw [node110_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node112_check : node112 =
    Integer.Sparse.merge node109 node111 := by decide +kernel

theorem node112_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node112 x = ((((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x) + (((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x + (((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + ((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x))) := by
  rw [node112_check, Integer.Sparse.eval_merge]
  rw [node109_eval, node111_eval]

theorem node113_check : node113 =
    Integer.Sparse.merge (Integer.Sparse.scale (-137926) entry_5_16) (Integer.Sparse.scale (5235805) entry_5_17) := by decide +kernel

theorem node113_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node113 x = (((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x) := by
  rw [node113_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node114_check : node114 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3714554) entry_5_15) node113 := by decide +kernel

theorem node114_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node114 x = (((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x + (((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x)) := by
  rw [node114_check, Integer.Sparse.eval_merge]
  rw [node113_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node115_check : node115 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1888253) entry_5_19) (Integer.Sparse.scale (3409136) entry_5_20) := by decide +kernel

theorem node115_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node115 x = (((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + ((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x) := by
  rw [node115_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node116_check : node116 =
    Integer.Sparse.merge (Integer.Sparse.scale (250358) entry_5_18) node115 := by decide +kernel

theorem node116_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node116 x = (((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + (((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + ((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x)) := by
  rw [node116_check, Integer.Sparse.eval_merge]
  rw [node115_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node117_check : node117 =
    Integer.Sparse.merge node114 node116 := by decide +kernel

theorem node117_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node117 x = ((((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x + (((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x)) + (((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + (((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + ((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x))) := by
  rw [node117_check, Integer.Sparse.eval_merge]
  rw [node114_eval, node116_eval]

theorem node118_check : node118 =
    Integer.Sparse.merge node112 node117 := by decide +kernel

theorem node118_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node118 x = (((((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x) + (((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x + (((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + ((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x))) + ((((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x + (((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x)) + (((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + (((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + ((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x)))) := by
  rw [node118_check, Integer.Sparse.eval_merge]
  rw [node112_eval, node117_eval]

theorem node119_check : node119 =
    Integer.Sparse.merge node108 node118 := by decide +kernel

theorem node119_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x = ((((((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + ((-104535 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x) + (((1798169 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x + (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + ((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x))) + ((((4872019 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x + ((-2061591 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x) + (((173690 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + (((-125916 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x + ((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x)))) + (((((991536 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x + ((1695692 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x) + (((1212441 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x + (((-2053220 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + ((2143288 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x))) + ((((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x + (((-137926 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((5235805 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x)) + (((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + (((-1888253 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x + ((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x))))) := by
  rw [node119_check, Integer.Sparse.eval_merge]
  rw [node108_eval, node118_eval]

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

theorem row_eval_5_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x =
      ∑ j : Fin 21, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node119_eval]
  exact (sum_expand_21 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_5_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_5_e_oai
