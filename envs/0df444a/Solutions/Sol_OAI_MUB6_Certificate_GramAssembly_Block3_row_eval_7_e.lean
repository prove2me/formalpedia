-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:34:07.888085+00:00
-- url     : https://prove2.me/submissions/dbc9acce-6b13-4ead-ade5-4951ca4dd401

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E005
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node182_check : node182 =
    Integer.Sparse.merge (Integer.Sparse.scale (-35356) entry_7_1) (Integer.Sparse.scale (873692) entry_7_2) := by decide +kernel

theorem node182_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node182 x = (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x) := by
  rw [node182_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node183_check : node183 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6679308) entry_7_0) node182 := by decide +kernel

theorem node183_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node183 x = (((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) := by
  rw [node183_check, Integer.Sparse.eval_merge]
  rw [node182_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node184_check : node184 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4627001) entry_7_4) (Integer.Sparse.scale (2447831) entry_7_5) := by decide +kernel

theorem node184_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node184 x = (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x) := by
  rw [node184_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node185_check : node185 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1883385) entry_7_3) node184 := by decide +kernel

theorem node185_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node185 x = (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x)) := by
  rw [node185_check, Integer.Sparse.eval_merge]
  rw [node184_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node186_check : node186 =
    Integer.Sparse.merge node183 node185 := by decide +kernel

theorem node186_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node186 x = ((((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) := by
  rw [node186_check, Integer.Sparse.eval_merge]
  rw [node183_eval, node185_eval]

theorem node187_check : node187 =
    Integer.Sparse.merge (Integer.Sparse.scale (7383368) entry_7_7) (Integer.Sparse.scale (-7671834) entry_7_8) := by decide +kernel

theorem node187_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node187 x = (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x) := by
  rw [node187_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node188_check : node188 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1569264) entry_7_6) node187 := by decide +kernel

theorem node188_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x = (((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) := by
  rw [node188_check, Integer.Sparse.eval_merge]
  rw [node187_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node189_check : node189 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6735967) entry_7_9) (Integer.Sparse.scale (118611) entry_7_10) := by decide +kernel

theorem node189_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node189 x = (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) := by
  rw [node189_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node190_check : node190 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3301327) entry_7_11) (Integer.Sparse.scale (-3540810) entry_7_12) := by decide +kernel

theorem node190_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node190 x = (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x) := by
  rw [node190_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node191_check : node191 =
    Integer.Sparse.merge node189 node190 := by decide +kernel

theorem node191_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node191 x = ((((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x)) := by
  rw [node191_check, Integer.Sparse.eval_merge]
  rw [node189_eval, node190_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node192_check : node192 =
    Integer.Sparse.merge node188 node191 := by decide +kernel

theorem node192_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node192 x = ((((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + ((((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x))) := by
  rw [node192_check, Integer.Sparse.eval_merge]
  rw [node188_eval, node191_eval]

theorem node193_check : node193 =
    Integer.Sparse.merge node186 node192 := by decide +kernel

theorem node193_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node193 x = (((((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) + ((((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + ((((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x)))) := by
  rw [node193_check, Integer.Sparse.eval_merge]
  rw [node186_eval, node192_eval]

theorem node194_check : node194 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1531264) entry_7_14) (Integer.Sparse.scale (-6992208) entry_7_15) := by decide +kernel

theorem node194_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node194 x = (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x) := by
  rw [node194_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node195_check : node195 =
    Integer.Sparse.merge (Integer.Sparse.scale (1566438) entry_7_13) node194 := by decide +kernel

theorem node195_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node195 x = (((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x)) := by
  rw [node195_check, Integer.Sparse.eval_merge]
  rw [node194_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node196_check : node196 =
    Integer.Sparse.merge (Integer.Sparse.scale (-99872) entry_7_16) (Integer.Sparse.scale (-5499711) entry_7_17) := by decide +kernel

theorem node196_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node196 x = (((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x) := by
  rw [node196_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node197_check : node197 =
    Integer.Sparse.merge (Integer.Sparse.scale (4157406) entry_7_18) (Integer.Sparse.scale (380152) entry_7_19) := by decide +kernel

theorem node197_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node197 x = (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + ((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x) := by
  rw [node197_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node198_check : node198 =
    Integer.Sparse.merge node196 node197 := by decide +kernel

theorem node198_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node198 x = ((((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x) + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + ((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x)) := by
  rw [node198_check, Integer.Sparse.eval_merge]
  rw [node196_eval, node197_eval]

theorem node199_check : node199 =
    Integer.Sparse.merge node195 node198 := by decide +kernel

theorem node199_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node199 x = ((((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x)) + ((((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x) + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + ((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x))) := by
  rw [node199_check, Integer.Sparse.eval_merge]
  rw [node195_eval, node198_eval]

theorem node200_check : node200 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8817786) entry_7_21) (Integer.Sparse.scale (-4896596) entry_7_22) := by decide +kernel

theorem node200_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node200 x = (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x + ((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_22 x) := by
  rw [node200_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node201_check : node201 =
    Integer.Sparse.merge (Integer.Sparse.scale (-257758) entry_7_20) node200 := by decide +kernel

theorem node201_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node201 x = (((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x + ((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_22 x)) := by
  rw [node201_check, Integer.Sparse.eval_merge]
  rw [node200_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node202_check : node202 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1431032) entry_7_23) (Integer.Sparse.scale (-1723883) entry_7_24) := by decide +kernel

theorem node202_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node202 x = (((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_23 x + ((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_24 x) := by
  rw [node202_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node203_check : node203 =
    Integer.Sparse.merge (Integer.Sparse.scale (4284472) entry_7_25) (Integer.Sparse.scale (2854925) entry_7_26) := by decide +kernel

theorem node203_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node203 x = (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_25 x + ((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_26 x) := by
  rw [node203_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node204_check : node204 =
    Integer.Sparse.merge node202 node203 := by decide +kernel

theorem node204_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node204 x = ((((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_23 x + ((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_24 x) + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_25 x + ((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_26 x)) := by
  rw [node204_check, Integer.Sparse.eval_merge]
  rw [node202_eval, node203_eval]

theorem node205_check : node205 =
    Integer.Sparse.merge node201 node204 := by decide +kernel

theorem node205_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node205 x = ((((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x + ((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_22 x)) + ((((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_23 x + ((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_24 x) + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_25 x + ((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_26 x))) := by
  rw [node205_check, Integer.Sparse.eval_merge]
  rw [node201_eval, node204_eval]

theorem node206_check : node206 =
    Integer.Sparse.merge node199 node205 := by decide +kernel

theorem node206_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node206 x = (((((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x)) + ((((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x) + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + ((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x))) + ((((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x + ((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_22 x)) + ((((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_23 x + ((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_24 x) + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_25 x + ((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_26 x)))) := by
  rw [node206_check, Integer.Sparse.eval_merge]
  rw [node199_eval, node205_eval]

theorem node207_check : node207 =
    Integer.Sparse.merge node193 node206 := by decide +kernel

theorem node207_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node207 x = ((((((-6679308 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_0 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_1 x + ((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_2 x)) + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_3 x + (((-4627001 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_4 x + ((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_5 x))) + ((((-1569264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_6 x + (((7383368 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_7 x + ((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_8 x)) + ((((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_9 x + ((118611 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_10 x) + (((-3301327 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_11 x + ((-3540810 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_12 x)))) + (((((1566438 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_13 x + (((-1531264 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_14 x + ((-6992208 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_15 x)) + ((((-99872 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_16 x + ((-5499711 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_17 x) + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_18 x + ((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_19 x))) + ((((-257758 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_20 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_21 x + ((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_22 x)) + ((((-1431032 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_23 x + ((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_24 x) + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_25 x + ((2854925 : ℤ) : ℝ) * Integer.Sparse.eval entry_7_26 x))))) := by
  rw [node207_check, Integer.Sparse.eval_merge]
  rw [node193_eval, node206_eval]

end MUB6.Certificate.GramAssembly.Block3

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

theorem sum_expand_27 {R : Type*} [AddCommMonoid R] (F : Fin 27 → R) :
    (∑ i, F i) = ((((F 0 + (F 1 + F 2)) + (F 3 + (F 4 + F 5))) + ((F 6 + (F 7 + F 8)) + ((F 9 + F 10) + (F 11 + F 12)))) + (((F 13 + (F 14 + F 15)) + ((F 16 + F 17) + (F 18 + F 19))) + ((F 20 + (F 21 + F 22)) + ((F 23 + F 24) + (F 25 + F 26))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (F 0 + (F 1 + (F 2 + (F 3 + (F 4 + (F 5 + (F 6 + (F 7 + (F 8 + (F 9 + (F 10 + (F 11 + (F 12 + (F 13 + (F 14 + (F 15 + (F 16 + (F 17 + (F 18 + (F 19 + (F 20 + (F 21 + (F 22 + (F 23 + (F 24 + (F 25 + (F 26 + 0))))))))))))))))))))))))))) = ((((F 0 + (F 1 + F 2)) + (F 3 + (F 4 + F 5))) + ((F 6 + (F 7 + F 8)) + ((F 9 + F 10) + (F 11 + F 12)))) + (((F 13 + (F 14 + F 15)) + ((F 16 + F 17) + (F 18 + F 19))) + ((F 20 + (F 21 + F 22)) + ((F 23 + F 24) + (F 25 + F 26)))))
  simp only [add_zero, add_assoc]

end MUB6.Certificate.GramAssembly

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

theorem row_eval_7_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node207 x =
      ∑ j : Fin 27, (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x := by
  rw [node207_eval]
  exact (sum_expand_27 (fun j => (weights 7 j : ℝ) * Integer.Sparse.eval (entries 7 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_7_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_7_e_oai
