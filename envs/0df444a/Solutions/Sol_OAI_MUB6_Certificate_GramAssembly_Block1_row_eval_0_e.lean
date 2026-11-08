-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:12.920145+00:00
-- url     : https://prove2.me/submissions/657eed77-e38d-4f6d-aaca-6e944b5bca69

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node0_check : node0 =
    Integer.Sparse.merge (Integer.Sparse.scale (8281974) entry_0_0) (Integer.Sparse.scale (317457) entry_0_1) := by decide +kernel

theorem node0_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node0 x = (((8281974 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) := by
  rw [node0_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node1_check : node1 =
    Integer.Sparse.merge (Integer.Sparse.scale (591578) entry_0_3) (Integer.Sparse.scale (-3564906) entry_0_4) := by decide +kernel

theorem node1_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node1 x = (((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x) := by
  rw [node1_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node2_check : node2 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4538959) entry_0_2) node1 := by decide +kernel

theorem node2_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node2 x = (((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x)) := by
  rw [node2_check, Integer.Sparse.eval_merge]
  rw [node1_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node3_check : node3 =
    Integer.Sparse.merge node0 node2 := by decide +kernel

theorem node3_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node3 x = ((((8281974 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) := by
  rw [node3_check, Integer.Sparse.eval_merge]
  rw [node0_eval, node2_eval]

theorem node4_check : node4 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1637779) entry_0_5) (Integer.Sparse.scale (2692899) entry_0_6) := by decide +kernel

theorem node4_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node4 x = (((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + ((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x) := by
  rw [node4_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node5_check : node5 =
    Integer.Sparse.merge (Integer.Sparse.scale (144765) entry_0_8) (Integer.Sparse.scale (-6253927) entry_0_9) := by decide +kernel

theorem node5_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node5 x = (((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + ((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x) := by
  rw [node5_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node6_check : node6 =
    Integer.Sparse.merge (Integer.Sparse.scale (-164059) entry_0_7) node5 := by decide +kernel

theorem node6_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node6 x = (((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + (((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + ((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x)) := by
  rw [node6_check, Integer.Sparse.eval_merge]
  rw [node5_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node7_check : node7 =
    Integer.Sparse.merge node4 node6 := by decide +kernel

theorem node7_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node7 x = ((((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + ((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x) + (((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + (((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + ((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x))) := by
  rw [node7_check, Integer.Sparse.eval_merge]
  rw [node4_eval, node6_eval]

theorem node8_check : node8 =
    Integer.Sparse.merge node3 node7 := by decide +kernel

theorem node8_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node8 x = (((((8281974 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) + ((((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + ((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x) + (((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + (((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + ((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x)))) := by
  rw [node8_check, Integer.Sparse.eval_merge]
  rw [node3_eval, node7_eval]

theorem node9_check : node9 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1632149) entry_0_10) (Integer.Sparse.scale (-1203380) entry_0_11) := by decide +kernel

theorem node9_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node9 x = (((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x) := by
  rw [node9_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node10_check : node10 =
    Integer.Sparse.merge (Integer.Sparse.scale (1265023) entry_0_13) (Integer.Sparse.scale (-3980129) entry_0_14) := by decide +kernel

theorem node10_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node10 x = (((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + ((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x) := by
  rw [node10_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node11_check : node11 =
    Integer.Sparse.merge (Integer.Sparse.scale (208493) entry_0_12) node10 := by decide +kernel

theorem node11_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node11 x = (((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x + (((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + ((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x)) := by
  rw [node11_check, Integer.Sparse.eval_merge]
  rw [node10_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node12_check : node12 =
    Integer.Sparse.merge node9 node11 := by decide +kernel

theorem node12_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node12 x = ((((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x) + (((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x + (((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + ((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x))) := by
  rw [node12_check, Integer.Sparse.eval_merge]
  rw [node9_eval, node11_eval]

theorem node13_check : node13 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5318840) entry_0_16) (Integer.Sparse.scale (-2763722) entry_0_17) := by decide +kernel

theorem node13_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node13 x = (((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x) := by
  rw [node13_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node14_check : node14 =
    Integer.Sparse.merge (Integer.Sparse.scale (4968645) entry_0_15) node13 := by decide +kernel

theorem node14_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node14 x = (((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x + (((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x)) := by
  rw [node14_check, Integer.Sparse.eval_merge]
  rw [node13_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node15_check : node15 =
    Integer.Sparse.merge (Integer.Sparse.scale (1101122) entry_0_19) (Integer.Sparse.scale (-8259767) entry_0_20) := by decide +kernel

theorem node15_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node15 x = (((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + ((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x) := by
  rw [node15_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node16_check : node16 =
    Integer.Sparse.merge (Integer.Sparse.scale (2313302) entry_0_18) node15 := by decide +kernel

theorem node16_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node16 x = (((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + (((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + ((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x)) := by
  rw [node16_check, Integer.Sparse.eval_merge]
  rw [node15_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node17_check : node17 =
    Integer.Sparse.merge node14 node16 := by decide +kernel

theorem node17_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node17 x = ((((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x + (((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x)) + (((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + (((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + ((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x))) := by
  rw [node17_check, Integer.Sparse.eval_merge]
  rw [node14_eval, node16_eval]

theorem node18_check : node18 =
    Integer.Sparse.merge node12 node17 := by decide +kernel

theorem node18_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node18 x = (((((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x) + (((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x + (((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + ((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x))) + ((((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x + (((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x)) + (((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + (((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + ((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x)))) := by
  rw [node18_check, Integer.Sparse.eval_merge]
  rw [node12_eval, node17_eval]

theorem node19_check : node19 =
    Integer.Sparse.merge node8 node18 := by decide +kernel

theorem node19_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x = ((((((8281974 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_0 x + ((317457 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_1 x) + (((-4538959 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_2 x + (((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_3 x + ((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_4 x))) + ((((-1637779 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_5 x + ((2692899 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_6 x) + (((-164059 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_7 x + (((144765 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_8 x + ((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_9 x)))) + (((((-1632149 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_10 x + ((-1203380 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_11 x) + (((208493 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_12 x + (((1265023 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_13 x + ((-3980129 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_14 x))) + ((((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_15 x + (((-5318840 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_16 x + ((-2763722 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_17 x)) + (((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_18 x + (((1101122 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_19 x + ((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_0_20 x))))) := by
  rw [node19_check, Integer.Sparse.eval_merge]
  rw [node8_eval, node18_eval]

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

theorem row_eval_0_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node19 x =
      ∑ j : Fin 21, (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x := by
  rw [node19_eval]
  exact (sum_expand_21 (fun j => (weights 0 j : ℝ) * Integer.Sparse.eval (entries 0 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_0_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_0_e_oai
