-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:17.390543+00:00
-- url     : https://prove2.me/submissions/698f9878-b04e-4643-bf99-c3b063514a34

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E173
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node300_check : node300 =
    Integer.Sparse.merge (Integer.Sparse.scale (4968645) entry_15_0) (Integer.Sparse.scale (-1358640) entry_15_1) := by decide +kernel

theorem node300_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node300 x = (((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) := by
  rw [node300_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node301_check : node301 =
    Integer.Sparse.merge (Integer.Sparse.scale (610565) entry_15_3) (Integer.Sparse.scale (-4006041) entry_15_4) := by decide +kernel

theorem node301_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node301 x = (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x) := by
  rw [node301_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node302_check : node302 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2556995) entry_15_2) node301 := by decide +kernel

theorem node302_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node302 x = (((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x)) := by
  rw [node302_check, Integer.Sparse.eval_merge]
  rw [node301_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node303_check : node303 =
    Integer.Sparse.merge node300 node302 := by decide +kernel

theorem node303_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node303 x = ((((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) + (((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x))) := by
  rw [node303_check, Integer.Sparse.eval_merge]
  rw [node300_eval, node302_eval]

theorem node304_check : node304 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3714554) entry_15_5) (Integer.Sparse.scale (6223125) entry_15_6) := by decide +kernel

theorem node304_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node304 x = (((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + ((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x) := by
  rw [node304_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node305_check : node305 =
    Integer.Sparse.merge (Integer.Sparse.scale (1575701) entry_15_8) (Integer.Sparse.scale (2667867) entry_15_9) := by decide +kernel

theorem node305_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node305 x = (((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + ((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x) := by
  rw [node305_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node306_check : node306 =
    Integer.Sparse.merge (Integer.Sparse.scale (-371680) entry_15_7) node305 := by decide +kernel

theorem node306_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node306 x = (((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + (((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + ((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x)) := by
  rw [node306_check, Integer.Sparse.eval_merge]
  rw [node305_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node307_check : node307 =
    Integer.Sparse.merge node304 node306 := by decide +kernel

theorem node307_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node307 x = ((((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + ((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x) + (((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + (((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + ((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x))) := by
  rw [node307_check, Integer.Sparse.eval_merge]
  rw [node304_eval, node306_eval]

theorem node308_check : node308 =
    Integer.Sparse.merge node303 node307 := by decide +kernel

theorem node308_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node308 x = (((((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) + (((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x))) + ((((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + ((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x) + (((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + (((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + ((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x)))) := by
  rw [node308_check, Integer.Sparse.eval_merge]
  rw [node303_eval, node307_eval]

theorem node309_check : node309 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2335848) entry_15_10) (Integer.Sparse.scale (-3265860) entry_15_11) := by decide +kernel

theorem node309_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node309 x = (((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x + ((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x) := by
  rw [node309_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node310_check : node310 =
    Integer.Sparse.merge (Integer.Sparse.scale (1774465) entry_15_13) (Integer.Sparse.scale (-4625257) entry_15_14) := by decide +kernel

theorem node310_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node310 x = (((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + ((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x) := by
  rw [node310_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node311_check : node311 =
    Integer.Sparse.merge (Integer.Sparse.scale (-16306805) entry_15_12) node310 := by decide +kernel

theorem node311_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node311 x = (((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x + (((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + ((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x)) := by
  rw [node311_check, Integer.Sparse.eval_merge]
  rw [node310_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node312_check : node312 =
    Integer.Sparse.merge node309 node311 := by decide +kernel

theorem node312_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node312 x = ((((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x + ((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x) + (((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x + (((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + ((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x))) := by
  rw [node312_check, Integer.Sparse.eval_merge]
  rw [node309_eval, node311_eval]

theorem node313_check : node313 =
    Integer.Sparse.merge (Integer.Sparse.scale (3981236) entry_15_16) (Integer.Sparse.scale (-3562699) entry_15_17) := by decide +kernel

theorem node313_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node313 x = (((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x) := by
  rw [node313_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node314_check : node314 =
    Integer.Sparse.merge (Integer.Sparse.scale (12672461) entry_15_15) node313 := by decide +kernel

theorem node314_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x = (((12672461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x + (((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x)) := by
  rw [node314_check, Integer.Sparse.eval_merge]
  rw [node313_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node315_check : node315 =
    Integer.Sparse.merge (Integer.Sparse.scale (3263582) entry_15_19) (Integer.Sparse.scale (-1351879) entry_15_20) := by decide +kernel

theorem node315_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node315 x = (((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + ((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x) := by
  rw [node315_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node316_check : node316 =
    Integer.Sparse.merge (Integer.Sparse.scale (12375243) entry_15_18) node315 := by decide +kernel

theorem node316_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node316 x = (((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + (((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + ((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x)) := by
  rw [node316_check, Integer.Sparse.eval_merge]
  rw [node315_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node317_check : node317 =
    Integer.Sparse.merge node314 node316 := by decide +kernel

theorem node317_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node317 x = ((((12672461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x + (((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x)) + (((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + (((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + ((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x))) := by
  rw [node317_check, Integer.Sparse.eval_merge]
  rw [node314_eval, node316_eval]

theorem node318_check : node318 =
    Integer.Sparse.merge node312 node317 := by decide +kernel

theorem node318_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node318 x = (((((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x + ((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x) + (((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x + (((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + ((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x))) + ((((12672461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x + (((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x)) + (((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + (((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + ((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x)))) := by
  rw [node318_check, Integer.Sparse.eval_merge]
  rw [node312_eval, node317_eval]

theorem node319_check : node319 =
    Integer.Sparse.merge node308 node318 := by decide +kernel

theorem node319_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x = ((((((4968645 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_0 x + ((-1358640 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_1 x) + (((-2556995 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_2 x + (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_3 x + ((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_4 x))) + ((((-3714554 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_5 x + ((6223125 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_6 x) + (((-371680 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_7 x + (((1575701 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_8 x + ((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_9 x)))) + (((((-2335848 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_10 x + ((-3265860 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_11 x) + (((-16306805 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_12 x + (((1774465 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_13 x + ((-4625257 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_14 x))) + ((((12672461 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_15 x + (((3981236 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_16 x + ((-3562699 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_17 x)) + (((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_18 x + (((3263582 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_19 x + ((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_15_20 x))))) := by
  rw [node319_check, Integer.Sparse.eval_merge]
  rw [node308_eval, node318_eval]

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

theorem row_eval_15_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x =
      ∑ j : Fin 21, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  rw [node319_eval]
  exact (sum_expand_21 (fun j => (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15_e_oai
