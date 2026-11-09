-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:29:32.081194+00:00
-- url     : https://prove2.me/submissions/ba8163c5-1dd9-4ce3-a3ea-ac1ccac123fc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E005
import Definitions.Def_OAIQ106E006
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node546_check : node546 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1198268) entry_21_1) (Integer.Sparse.scale (-1590279) entry_21_2) := by decide +kernel

theorem node546_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node546 x = (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x + ((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x) := by
  rw [node546_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node547_check : node547 =
    Integer.Sparse.merge (Integer.Sparse.scale (14265487) entry_21_0) node546 := by decide +kernel

theorem node547_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node547 x = (((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x + ((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x)) := by
  rw [node547_check, Integer.Sparse.eval_merge]
  rw [node546_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node548_check : node548 =
    Integer.Sparse.merge (Integer.Sparse.scale (6508035) entry_21_4) (Integer.Sparse.scale (-2391480) entry_21_5) := by decide +kernel

theorem node548_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node548 x = (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x + ((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x) := by
  rw [node548_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node549_check : node549 =
    Integer.Sparse.merge (Integer.Sparse.scale (2837114) entry_21_3) node548 := by decide +kernel

theorem node549_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node549 x = (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x + ((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x)) := by
  rw [node549_check, Integer.Sparse.eval_merge]
  rw [node548_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node550_check : node550 =
    Integer.Sparse.merge node547 node549 := by decide +kernel

theorem node550_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node550 x = ((((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x + ((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x)) + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x + ((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x))) := by
  rw [node550_check, Integer.Sparse.eval_merge]
  rw [node547_eval, node549_eval]

theorem node551_check : node551 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8817786) entry_21_7) (Integer.Sparse.scale (11010772) entry_21_8) := by decide +kernel

theorem node551_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node551 x = (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x + ((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x) := by
  rw [node551_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node552_check : node552 =
    Integer.Sparse.merge (Integer.Sparse.scale (3554996) entry_21_6) node551 := by decide +kernel

theorem node552_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node552 x = (((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x + ((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x)) := by
  rw [node552_check, Integer.Sparse.eval_merge]
  rw [node551_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node553_check : node553 =
    Integer.Sparse.merge (Integer.Sparse.scale (4755447) entry_21_9) (Integer.Sparse.scale (1772760) entry_21_10) := by decide +kernel

theorem node553_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node553 x = (((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x) := by
  rw [node553_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node554_check : node554 =
    Integer.Sparse.merge (Integer.Sparse.scale (4701210) entry_21_11) (Integer.Sparse.scale (7981741) entry_21_12) := by decide +kernel

theorem node554_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node554 x = (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x) := by
  rw [node554_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node555_check : node555 =
    Integer.Sparse.merge node553 node554 := by decide +kernel

theorem node555_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node555 x = ((((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x) + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x)) := by
  rw [node555_check, Integer.Sparse.eval_merge]
  rw [node553_eval, node554_eval]

theorem node556_check : node556 =
    Integer.Sparse.merge node552 node555 := by decide +kernel

theorem node556_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node556 x = ((((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x + ((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x)) + ((((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x) + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x))) := by
  rw [node556_check, Integer.Sparse.eval_merge]
  rw [node552_eval, node555_eval]

theorem node557_check : node557 =
    Integer.Sparse.merge node550 node556 := by decide +kernel

theorem node557_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node557 x = (((((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x + ((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x)) + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x + ((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x))) + ((((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x + ((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x)) + ((((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x) + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x)))) := by
  rw [node557_check, Integer.Sparse.eval_merge]
  rw [node550_eval, node556_eval]

theorem node558_check : node558 =
    Integer.Sparse.merge (Integer.Sparse.scale (3595017) entry_21_14) (Integer.Sparse.scale (16030892) entry_21_15) := by decide +kernel

theorem node558_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node558 x = (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x) := by
  rw [node558_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node559_check : node559 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3987844) entry_21_13) node558 := by decide +kernel

theorem node559_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node559 x = (((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x)) := by
  rw [node559_check, Integer.Sparse.eval_merge]
  rw [node558_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node560_check : node560 =
    Integer.Sparse.merge (Integer.Sparse.scale (3762949) entry_21_16) (Integer.Sparse.scale (4428060) entry_21_17) := by decide +kernel

theorem node560_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node560 x = (((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + ((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x) := by
  rw [node560_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node561_check : node561 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8554511) entry_21_18) (Integer.Sparse.scale (-1690663) entry_21_19) := by decide +kernel

theorem node561_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node561 x = (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x + ((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x) := by
  rw [node561_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node562_check : node562 =
    Integer.Sparse.merge node560 node561 := by decide +kernel

theorem node562_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node562 x = ((((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + ((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x) + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x + ((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x)) := by
  rw [node562_check, Integer.Sparse.eval_merge]
  rw [node560_eval, node561_eval]

theorem node563_check : node563 =
    Integer.Sparse.merge node559 node562 := by decide +kernel

theorem node563_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node563 x = ((((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x)) + ((((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + ((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x) + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x + ((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x))) := by
  rw [node563_check, Integer.Sparse.eval_merge]
  rw [node559_eval, node562_eval]

theorem node564_check : node564 =
    Integer.Sparse.merge (Integer.Sparse.scale (32392892) entry_21_21) (Integer.Sparse.scale (11308744) entry_21_22) := by decide +kernel

theorem node564_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node564 x = (((32392892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x + ((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_22 x) := by
  rw [node564_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node565_check : node565 =
    Integer.Sparse.merge (Integer.Sparse.scale (954088) entry_21_20) node564 := by decide +kernel

theorem node565_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node565 x = (((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + (((32392892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x + ((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_22 x)) := by
  rw [node565_check, Integer.Sparse.eval_merge]
  rw [node564_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node566_check : node566 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3684421) entry_21_23) (Integer.Sparse.scale (-299084) entry_21_24) := by decide +kernel

theorem node566_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node566 x = (((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_23 x + ((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_24 x) := by
  rw [node566_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node567_check : node567 =
    Integer.Sparse.merge (Integer.Sparse.scale (-12045329) entry_21_25) (Integer.Sparse.scale (-8338454) entry_21_26) := by decide +kernel

theorem node567_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node567 x = (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_25 x + ((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_26 x) := by
  rw [node567_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node568_check : node568 =
    Integer.Sparse.merge node566 node567 := by decide +kernel

theorem node568_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node568 x = ((((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_23 x + ((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_24 x) + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_25 x + ((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_26 x)) := by
  rw [node568_check, Integer.Sparse.eval_merge]
  rw [node566_eval, node567_eval]

theorem node569_check : node569 =
    Integer.Sparse.merge node565 node568 := by decide +kernel

theorem node569_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node569 x = ((((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + (((32392892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x + ((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_22 x)) + ((((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_23 x + ((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_24 x) + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_25 x + ((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_26 x))) := by
  rw [node569_check, Integer.Sparse.eval_merge]
  rw [node565_eval, node568_eval]

theorem node570_check : node570 =
    Integer.Sparse.merge node563 node569 := by decide +kernel

theorem node570_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node570 x = (((((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x)) + ((((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + ((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x) + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x + ((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x))) + ((((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + (((32392892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x + ((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_22 x)) + ((((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_23 x + ((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_24 x) + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_25 x + ((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_26 x)))) := by
  rw [node570_check, Integer.Sparse.eval_merge]
  rw [node563_eval, node569_eval]

theorem node571_check : node571 =
    Integer.Sparse.merge node557 node570 := by decide +kernel

theorem node571_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node571 x = ((((((14265487 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x + ((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x)) + (((2837114 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + (((6508035 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x + ((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x))) + ((((3554996 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + (((-8817786 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x + ((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x)) + ((((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((1772760 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x) + (((4701210 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((7981741 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x)))) + (((((-3987844 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((3595017 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((16030892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x)) + ((((3762949 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + ((4428060 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x) + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x + ((-1690663 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x))) + ((((954088 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + (((32392892 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x + ((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_22 x)) + ((((-3684421 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_23 x + ((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_24 x) + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_25 x + ((-8338454 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_26 x))))) := by
  rw [node571_check, Integer.Sparse.eval_merge]
  rw [node557_eval, node570_eval]

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

theorem row_eval_21_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node571 x =
      ∑ j : Fin 27, (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x := by
  rw [node571_eval]
  exact (sum_expand_27 (fun j => (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_21_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_21_e_oai
