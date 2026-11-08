-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:48.671879+00:00
-- url     : https://prove2.me/submissions/a0943e1f-08b0-4eb9-bf3b-78be85dc873b

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node294_check : node294 =
    Integer.Sparse.merge (Integer.Sparse.scale (12048267) entry_14_0) (Integer.Sparse.scale (10815796) entry_14_1) := by decide +kernel

theorem node294_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node294 x = (((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) := by
  rw [node294_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node295_check : node295 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7453387) entry_14_3) (Integer.Sparse.scale (4800575) entry_14_4) := by decide +kernel

theorem node295_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node295 x = (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x) := by
  rw [node295_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node296_check : node296 =
    Integer.Sparse.merge (Integer.Sparse.scale (15992020) entry_14_2) node295 := by decide +kernel

theorem node296_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node296 x = (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x)) := by
  rw [node296_check, Integer.Sparse.eval_merge]
  rw [node295_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node297_check : node297 =
    Integer.Sparse.merge node294 node296 := by decide +kernel

theorem node297_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node297 x = ((((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x))) := by
  rw [node297_check, Integer.Sparse.eval_merge]
  rw [node294_eval, node296_eval]

theorem node298_check : node298 =
    Integer.Sparse.merge (Integer.Sparse.scale (42159577) entry_14_6) (Integer.Sparse.scale (-4093860) entry_14_7) := by decide +kernel

theorem node298_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node298 x = (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + ((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x) := by
  rw [node298_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node299_check : node299 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6415795) entry_14_5) node298 := by decide +kernel

theorem node299_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node299 x = (((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + ((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x)) := by
  rw [node299_check, Integer.Sparse.eval_merge]
  rw [node298_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node300_check : node300 =
    Integer.Sparse.merge (Integer.Sparse.scale (2839721) entry_14_9) (Integer.Sparse.scale (40989979) entry_14_10) := by decide +kernel

theorem node300_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node300 x = (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x) := by
  rw [node300_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node301_check : node301 =
    Integer.Sparse.merge (Integer.Sparse.scale (21938238) entry_14_8) node300 := by decide +kernel

theorem node301_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node301 x = (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x)) := by
  rw [node301_check, Integer.Sparse.eval_merge]
  rw [node300_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node302_check : node302 =
    Integer.Sparse.merge node299 node301 := by decide +kernel

theorem node302_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node302 x = ((((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + ((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x)) + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x))) := by
  rw [node302_check, Integer.Sparse.eval_merge]
  rw [node299_eval, node301_eval]

theorem node303_check : node303 =
    Integer.Sparse.merge node297 node302 := by decide +kernel

theorem node303_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node303 x = (((((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x))) + ((((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + ((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x)) + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x)))) := by
  rw [node303_check, Integer.Sparse.eval_merge]
  rw [node297_eval, node302_eval]

theorem node304_check : node304 =
    Integer.Sparse.merge (Integer.Sparse.scale (9853406) entry_14_11) (Integer.Sparse.scale (-28830365) entry_14_12) := by decide +kernel

theorem node304_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node304 x = (((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x) := by
  rw [node304_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node305_check : node305 =
    Integer.Sparse.merge (Integer.Sparse.scale (58430304) entry_14_14) (Integer.Sparse.scale (28297024) entry_14_15) := by decide +kernel

theorem node305_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node305 x = (((58430304 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x) := by
  rw [node305_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node306_check : node306 =
    Integer.Sparse.merge (Integer.Sparse.scale (3479938) entry_14_13) node305 := by decide +kernel

theorem node306_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node306 x = (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((58430304 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x)) := by
  rw [node306_check, Integer.Sparse.eval_merge]
  rw [node305_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node307_check : node307 =
    Integer.Sparse.merge node304 node306 := by decide +kernel

theorem node307_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node307 x = ((((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x) + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((58430304 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x))) := by
  rw [node307_check, Integer.Sparse.eval_merge]
  rw [node304_eval, node306_eval]

theorem node308_check : node308 =
    Integer.Sparse.merge (Integer.Sparse.scale (6272171) entry_14_17) (Integer.Sparse.scale (-1826502) entry_14_18) := by decide +kernel

theorem node308_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node308 x = (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x + ((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x) := by
  rw [node308_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node309_check : node309 =
    Integer.Sparse.merge (Integer.Sparse.scale (-34667430) entry_14_16) node308 := by decide +kernel

theorem node309_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node309 x = (((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x + ((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x)) := by
  rw [node309_check, Integer.Sparse.eval_merge]
  rw [node308_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node310_check : node310 =
    Integer.Sparse.merge (Integer.Sparse.scale (4188233) entry_14_20) (Integer.Sparse.scale (11611437) entry_14_21) := by decide +kernel

theorem node310_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node310 x = (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + ((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x) := by
  rw [node310_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node311_check : node311 =
    Integer.Sparse.merge (Integer.Sparse.scale (-293742) entry_14_19) node310 := by decide +kernel

theorem node311_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node311 x = (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + ((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x)) := by
  rw [node311_check, Integer.Sparse.eval_merge]
  rw [node310_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node312_check : node312 =
    Integer.Sparse.merge node309 node311 := by decide +kernel

theorem node312_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node312 x = ((((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x + ((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x)) + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + ((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x))) := by
  rw [node312_check, Integer.Sparse.eval_merge]
  rw [node309_eval, node311_eval]

theorem node313_check : node313 =
    Integer.Sparse.merge node307 node312 := by decide +kernel

theorem node313_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node313 x = (((((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x) + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((58430304 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x))) + ((((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x + ((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x)) + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + ((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x)))) := by
  rw [node313_check, Integer.Sparse.eval_merge]
  rw [node307_eval, node312_eval]

theorem node314_check : node314 =
    Integer.Sparse.merge node303 node313 := by decide +kernel

theorem node314_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x = ((((((12048267 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_0 x + ((10815796 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_1 x) + (((15992020 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_2 x + (((-7453387 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_3 x + ((4800575 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_4 x))) + ((((-6415795 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_5 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_6 x + ((-4093860 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_7 x)) + (((21938238 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_8 x + (((2839721 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_9 x + ((40989979 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_10 x)))) + (((((9853406 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_11 x + ((-28830365 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_12 x) + (((3479938 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_13 x + (((58430304 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_14 x + ((28297024 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_15 x))) + ((((-34667430 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_16 x + (((6272171 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_17 x + ((-1826502 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_18 x)) + (((-293742 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_19 x + (((4188233 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_20 x + ((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_14_21 x))))) := by
  rw [node314_check, Integer.Sparse.eval_merge]
  rw [node303_eval, node313_eval]

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

theorem row_eval_14_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x =
      ∑ j : Fin 22, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  rw [node314_eval]
  exact (sum_expand_22 (fun j => (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x)).symm

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14_e_oai
