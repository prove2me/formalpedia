-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:30:50.843729+00:00
-- url     : https://prove2.me/submissions/c7b3a60a-cf14-480d-8ad3-1e3be71b4f0c

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

theorem node572_check : node572 =
    Integer.Sparse.merge (Integer.Sparse.scale (1132197) entry_22_1) (Integer.Sparse.scale (-234365) entry_22_2) := by decide +kernel

theorem node572_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node572 x = (((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_1 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_2 x) := by
  rw [node572_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node573_check : node573 =
    Integer.Sparse.merge (Integer.Sparse.scale (26849611) entry_22_0) node572 := by decide +kernel

theorem node573_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node573 x = (((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_0 x + (((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_1 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_2 x)) := by
  rw [node573_check, Integer.Sparse.eval_merge]
  rw [node572_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node574_check : node574 =
    Integer.Sparse.merge (Integer.Sparse.scale (2071984) entry_22_4) (Integer.Sparse.scale (1842073) entry_22_5) := by decide +kernel

theorem node574_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node574 x = (((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_4 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_5 x) := by
  rw [node574_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node575_check : node575 =
    Integer.Sparse.merge (Integer.Sparse.scale (17953246) entry_22_3) node574 := by decide +kernel

theorem node575_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node575 x = (((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_3 x + (((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_4 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_5 x)) := by
  rw [node575_check, Integer.Sparse.eval_merge]
  rw [node574_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node576_check : node576 =
    Integer.Sparse.merge node573 node575 := by decide +kernel

theorem node576_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node576 x = ((((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_0 x + (((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_1 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_2 x)) + (((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_3 x + (((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_4 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_5 x))) := by
  rw [node576_check, Integer.Sparse.eval_merge]
  rw [node573_eval, node575_eval]

theorem node577_check : node577 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4896596) entry_22_7) (Integer.Sparse.scale (7616015) entry_22_8) := by decide +kernel

theorem node577_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node577 x = (((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_7 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_8 x) := by
  rw [node577_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node578_check : node578 =
    Integer.Sparse.merge (Integer.Sparse.scale (-10414524) entry_22_6) node577 := by decide +kernel

theorem node578_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node578 x = (((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_6 x + (((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_7 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_8 x)) := by
  rw [node578_check, Integer.Sparse.eval_merge]
  rw [node577_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node579_check : node579 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1246459) entry_22_9) (Integer.Sparse.scale (18979737) entry_22_10) := by decide +kernel

theorem node579_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node579 x = (((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_9 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_10 x) := by
  rw [node579_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node580_check : node580 =
    Integer.Sparse.merge (Integer.Sparse.scale (16943621) entry_22_11) (Integer.Sparse.scale (9023959) entry_22_12) := by decide +kernel

theorem node580_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node580 x = (((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_11 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_12 x) := by
  rw [node580_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node581_check : node581 =
    Integer.Sparse.merge node579 node580 := by decide +kernel

theorem node581_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node581 x = ((((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_9 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_10 x) + (((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_11 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_12 x)) := by
  rw [node581_check, Integer.Sparse.eval_merge]
  rw [node579_eval, node580_eval]

theorem node582_check : node582 =
    Integer.Sparse.merge node578 node581 := by decide +kernel

theorem node582_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node582 x = ((((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_6 x + (((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_7 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_8 x)) + ((((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_9 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_10 x) + (((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_11 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_12 x))) := by
  rw [node582_check, Integer.Sparse.eval_merge]
  rw [node578_eval, node581_eval]

theorem node583_check : node583 =
    Integer.Sparse.merge node576 node582 := by decide +kernel

theorem node583_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node583 x = (((((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_0 x + (((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_1 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_2 x)) + (((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_3 x + (((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_4 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_5 x))) + ((((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_6 x + (((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_7 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_8 x)) + ((((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_9 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_10 x) + (((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_11 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_12 x)))) := by
  rw [node583_check, Integer.Sparse.eval_merge]
  rw [node576_eval, node582_eval]

theorem node584_check : node584 =
    Integer.Sparse.merge (Integer.Sparse.scale (-827728) entry_22_14) (Integer.Sparse.scale (-22856504) entry_22_15) := by decide +kernel

theorem node584_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node584 x = (((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_14 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_15 x) := by
  rw [node584_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node585_check : node585 =
    Integer.Sparse.merge (Integer.Sparse.scale (-147587) entry_22_13) node584 := by decide +kernel

theorem node585_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node585 x = (((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_13 x + (((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_14 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_15 x)) := by
  rw [node585_check, Integer.Sparse.eval_merge]
  rw [node584_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node586_check : node586 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9242889) entry_22_16) (Integer.Sparse.scale (-8076457) entry_22_17) := by decide +kernel

theorem node586_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node586 x = (((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_16 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_17 x) := by
  rw [node586_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node587_check : node587 =
    Integer.Sparse.merge (Integer.Sparse.scale (-16299324) entry_22_18) (Integer.Sparse.scale (32194445) entry_22_19) := by decide +kernel

theorem node587_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node587 x = (((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_18 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_19 x) := by
  rw [node587_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node588_check : node588 =
    Integer.Sparse.merge node586 node587 := by decide +kernel

theorem node588_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node588 x = ((((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_16 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_17 x) + (((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_18 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_19 x)) := by
  rw [node588_check, Integer.Sparse.eval_merge]
  rw [node586_eval, node587_eval]

theorem node589_check : node589 =
    Integer.Sparse.merge node585 node588 := by decide +kernel

theorem node589_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node589 x = ((((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_13 x + (((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_14 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_15 x)) + ((((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_16 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_17 x) + (((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_18 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_19 x))) := by
  rw [node589_check, Integer.Sparse.eval_merge]
  rw [node585_eval, node588_eval]

theorem node590_check : node590 =
    Integer.Sparse.merge (Integer.Sparse.scale (11308744) entry_22_21) (Integer.Sparse.scale (76533185) entry_22_22) := by decide +kernel

theorem node590_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node590 x = (((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_21 x + ((76533185 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_22 x) := by
  rw [node590_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node591_check : node591 =
    Integer.Sparse.merge (Integer.Sparse.scale (1261245) entry_22_20) node590 := by decide +kernel

theorem node591_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node591 x = (((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_20 x + (((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_21 x + ((76533185 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_22 x)) := by
  rw [node591_check, Integer.Sparse.eval_merge]
  rw [node590_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node592_check : node592 =
    Integer.Sparse.merge (Integer.Sparse.scale (-18865439) entry_22_23) (Integer.Sparse.scale (7037228) entry_22_24) := by decide +kernel

theorem node592_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node592 x = (((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_23 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_24 x) := by
  rw [node592_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node593_check : node593 =
    Integer.Sparse.merge (Integer.Sparse.scale (-20572372) entry_22_25) (Integer.Sparse.scale (-5290054) entry_22_26) := by decide +kernel

theorem node593_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node593 x = (((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_25 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_26 x) := by
  rw [node593_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node594_check : node594 =
    Integer.Sparse.merge node592 node593 := by decide +kernel

theorem node594_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node594 x = ((((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_23 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_24 x) + (((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_25 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_26 x)) := by
  rw [node594_check, Integer.Sparse.eval_merge]
  rw [node592_eval, node593_eval]

theorem node595_check : node595 =
    Integer.Sparse.merge node591 node594 := by decide +kernel

theorem node595_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node595 x = ((((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_20 x + (((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_21 x + ((76533185 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_22 x)) + ((((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_23 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_24 x) + (((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_25 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_26 x))) := by
  rw [node595_check, Integer.Sparse.eval_merge]
  rw [node591_eval, node594_eval]

theorem node596_check : node596 =
    Integer.Sparse.merge node589 node595 := by decide +kernel

theorem node596_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node596 x = (((((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_13 x + (((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_14 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_15 x)) + ((((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_16 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_17 x) + (((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_18 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_19 x))) + ((((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_20 x + (((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_21 x + ((76533185 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_22 x)) + ((((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_23 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_24 x) + (((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_25 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_26 x)))) := by
  rw [node596_check, Integer.Sparse.eval_merge]
  rw [node589_eval, node595_eval]

theorem node597_check : node597 =
    Integer.Sparse.merge node583 node596 := by decide +kernel

theorem node597_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node597 x = ((((((26849611 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_0 x + (((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_1 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_2 x)) + (((17953246 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_3 x + (((2071984 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_4 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_5 x))) + ((((-10414524 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_6 x + (((-4896596 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_7 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_8 x)) + ((((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_9 x + ((18979737 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_10 x) + (((16943621 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_11 x + ((9023959 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_12 x)))) + (((((-147587 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_13 x + (((-827728 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_14 x + ((-22856504 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_15 x)) + ((((-9242889 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_16 x + ((-8076457 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_17 x) + (((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_18 x + ((32194445 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_19 x))) + ((((1261245 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_20 x + (((11308744 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_21 x + ((76533185 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_22 x)) + ((((-18865439 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_23 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_24 x) + (((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_25 x + ((-5290054 : ℤ) : ℝ) * Integer.Sparse.eval entry_22_26 x))))) := by
  rw [node597_check, Integer.Sparse.eval_merge]
  rw [node583_eval, node596_eval]

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

theorem row_eval_22_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node597 x =
      ∑ j : Fin 27, (weights 22 j : ℝ) * Integer.Sparse.eval (entries 22 j) x := by
  rw [node597_eval]
  exact (sum_expand_27 (fun j => (weights 22 j : ℝ) * Integer.Sparse.eval (entries 22 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_22_e_oai
