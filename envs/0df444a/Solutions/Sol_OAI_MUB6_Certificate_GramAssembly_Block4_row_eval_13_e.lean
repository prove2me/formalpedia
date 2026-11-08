-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:44.785863+00:00
-- url     : https://prove2.me/submissions/49354267-4c9d-4033-914e-7fab4f5a76d7

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node273_check : node273 =
    Integer.Sparse.merge (Integer.Sparse.scale (-653324) entry_13_0) (Integer.Sparse.scale (3042363) entry_13_1) := by decide +kernel

theorem node273_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node273 x = (((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) := by
  rw [node273_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node274_check : node274 =
    Integer.Sparse.merge (Integer.Sparse.scale (3371581) entry_13_3) (Integer.Sparse.scale (2934355) entry_13_4) := by decide +kernel

theorem node274_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node274 x = (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x) := by
  rw [node274_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node275_check : node275 =
    Integer.Sparse.merge (Integer.Sparse.scale (533958) entry_13_2) node274 := by decide +kernel

theorem node275_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node275 x = (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x)) := by
  rw [node275_check, Integer.Sparse.eval_merge]
  rw [node274_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node276_check : node276 =
    Integer.Sparse.merge node273 node275 := by decide +kernel

theorem node276_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node276 x = ((((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) + (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x))) := by
  rw [node276_check, Integer.Sparse.eval_merge]
  rw [node273_eval, node275_eval]

theorem node277_check : node277 =
    Integer.Sparse.merge (Integer.Sparse.scale (-826686) entry_13_6) (Integer.Sparse.scale (1492337) entry_13_7) := by decide +kernel

theorem node277_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node277 x = (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + ((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x) := by
  rw [node277_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node278_check : node278 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1757350) entry_13_5) node277 := by decide +kernel

theorem node278_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node278 x = (((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + ((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x)) := by
  rw [node278_check, Integer.Sparse.eval_merge]
  rw [node277_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node279_check : node279 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1050249) entry_13_9) (Integer.Sparse.scale (11108282) entry_13_10) := by decide +kernel

theorem node279_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node279 x = (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x) := by
  rw [node279_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node280_check : node280 =
    Integer.Sparse.merge (Integer.Sparse.scale (2684271) entry_13_8) node279 := by decide +kernel

theorem node280_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node280 x = (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x)) := by
  rw [node280_check, Integer.Sparse.eval_merge]
  rw [node279_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node281_check : node281 =
    Integer.Sparse.merge node278 node280 := by decide +kernel

theorem node281_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node281 x = ((((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + ((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x)) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x))) := by
  rw [node281_check, Integer.Sparse.eval_merge]
  rw [node278_eval, node280_eval]

theorem node282_check : node282 =
    Integer.Sparse.merge node276 node281 := by decide +kernel

theorem node282_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node282 x = (((((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) + (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x))) + ((((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + ((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x)) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x)))) := by
  rw [node282_check, Integer.Sparse.eval_merge]
  rw [node276_eval, node281_eval]

theorem node283_check : node283 =
    Integer.Sparse.merge (Integer.Sparse.scale (4853940) entry_13_11) (Integer.Sparse.scale (-2209331) entry_13_12) := by decide +kernel

theorem node283_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node283 x = (((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x) := by
  rw [node283_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node284_check : node284 =
    Integer.Sparse.merge (Integer.Sparse.scale (3479938) entry_13_14) (Integer.Sparse.scale (4913859) entry_13_15) := by decide +kernel

theorem node284_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node284 x = (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x) := by
  rw [node284_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node285_check : node285 =
    Integer.Sparse.merge (Integer.Sparse.scale (12676281) entry_13_13) node284 := by decide +kernel

theorem node285_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node285 x = (((12676281 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x)) := by
  rw [node285_check, Integer.Sparse.eval_merge]
  rw [node284_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node286_check : node286 =
    Integer.Sparse.merge node283 node285 := by decide +kernel

theorem node286_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node286 x = ((((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x) + (((12676281 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x))) := by
  rw [node286_check, Integer.Sparse.eval_merge]
  rw [node283_eval, node285_eval]

theorem node287_check : node287 =
    Integer.Sparse.merge (Integer.Sparse.scale (2169781) entry_13_17) (Integer.Sparse.scale (-175103) entry_13_18) := by decide +kernel

theorem node287_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node287 x = (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x + ((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x) := by
  rw [node287_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node288_check : node288 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8763480) entry_13_16) node287 := by decide +kernel

theorem node288_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node288 x = (((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x + ((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x)) := by
  rw [node288_check, Integer.Sparse.eval_merge]
  rw [node287_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node289_check : node289 =
    Integer.Sparse.merge (Integer.Sparse.scale (-575196) entry_13_20) (Integer.Sparse.scale (7485003) entry_13_21) := by decide +kernel

theorem node289_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node289 x = (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + ((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x) := by
  rw [node289_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node290_check : node290 =
    Integer.Sparse.merge (Integer.Sparse.scale (28798) entry_13_19) node289 := by decide +kernel

theorem node290_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node290 x = (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + ((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x)) := by
  rw [node290_check, Integer.Sparse.eval_merge]
  rw [node289_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node291_check : node291 =
    Integer.Sparse.merge node288 node290 := by decide +kernel

theorem node291_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node291 x = ((((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x + ((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x)) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + ((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x))) := by
  rw [node291_check, Integer.Sparse.eval_merge]
  rw [node288_eval, node290_eval]

theorem node292_check : node292 =
    Integer.Sparse.merge node286 node291 := by decide +kernel

theorem node292_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node292 x = (((((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x) + (((12676281 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x))) + ((((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x + ((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x)) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + ((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x)))) := by
  rw [node292_check, Integer.Sparse.eval_merge]
  rw [node286_eval, node291_eval]

theorem node293_check : node293 =
    Integer.Sparse.merge node282 node292 := by decide +kernel

theorem node293_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node293 x = ((((((-653324 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_0 x + ((3042363 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_1 x) + (((533958 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_2 x + (((3371581 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_3 x + ((2934355 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_4 x))) + ((((-1757350 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_5 x + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_6 x + ((1492337 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_7 x)) + (((2684271 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_8 x + (((-1050249 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_9 x + ((11108282 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_10 x)))) + (((((4853940 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_11 x + ((-2209331 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_12 x) + (((12676281 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_13 x + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_14 x + ((4913859 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_15 x))) + ((((-8763480 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_16 x + (((2169781 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_17 x + ((-175103 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_18 x)) + (((28798 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_19 x + (((-575196 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_20 x + ((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_13_21 x))))) := by
  rw [node293_check, Integer.Sparse.eval_merge]
  rw [node282_eval, node292_eval]

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

theorem row_eval_13_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node293 x =
      ∑ j : Fin 22, (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x := by
  rw [node293_eval]
  exact (sum_expand_22 (fun j => (weights 13 j : ℝ) * Integer.Sparse.eval (entries 13 j) x)).symm

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_13_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_13_e_oai
