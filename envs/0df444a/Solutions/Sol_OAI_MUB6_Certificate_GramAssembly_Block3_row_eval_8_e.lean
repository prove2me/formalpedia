-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:43:58.813037+00:00
-- url     : https://prove2.me/submissions/2592fe14-cabe-438d-9b34-38b7a8c69d9d

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node208_check : node208 =
    Integer.Sparse.merge (Integer.Sparse.scale (-831071) entry_8_1) (Integer.Sparse.scale (-2456751) entry_8_2) := by decide +kernel

theorem node208_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node208 x = (((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x) := by
  rw [node208_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node209_check : node209 =
    Integer.Sparse.merge (Integer.Sparse.scale (8323724) entry_8_0) node208 := by decide +kernel

theorem node209_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node209 x = (((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) := by
  rw [node209_check, Integer.Sparse.eval_merge]
  rw [node208_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node210_check : node210 =
    Integer.Sparse.merge (Integer.Sparse.scale (7215886) entry_8_4) (Integer.Sparse.scale (-2470731) entry_8_5) := by decide +kernel

theorem node210_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node210 x = (((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x) := by
  rw [node210_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node211_check : node211 =
    Integer.Sparse.merge (Integer.Sparse.scale (-68139) entry_8_3) node210 := by decide +kernel

theorem node211_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node211 x = (((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x)) := by
  rw [node211_check, Integer.Sparse.eval_merge]
  rw [node210_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node212_check : node212 =
    Integer.Sparse.merge node209 node211 := by decide +kernel

theorem node212_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node212 x = ((((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) := by
  rw [node212_check, Integer.Sparse.eval_merge]
  rw [node209_eval, node211_eval]

theorem node213_check : node213 =
    Integer.Sparse.merge (Integer.Sparse.scale (-7671834) entry_8_7) (Integer.Sparse.scale (20205267) entry_8_8) := by decide +kernel

theorem node213_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node213 x = (((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((20205267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x) := by
  rw [node213_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node214_check : node214 =
    Integer.Sparse.merge (Integer.Sparse.scale (3004866) entry_8_6) node213 := by decide +kernel

theorem node214_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node214 x = (((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((20205267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) := by
  rw [node214_check, Integer.Sparse.eval_merge]
  rw [node213_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node215_check : node215 =
    Integer.Sparse.merge (Integer.Sparse.scale (10681732) entry_8_9) (Integer.Sparse.scale (909816) entry_8_10) := by decide +kernel

theorem node215_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node215 x = (((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) := by
  rw [node215_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node216_check : node216 =
    Integer.Sparse.merge (Integer.Sparse.scale (2492242) entry_8_11) (Integer.Sparse.scale (4317945) entry_8_12) := by decide +kernel

theorem node216_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node216 x = (((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x) := by
  rw [node216_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node217_check : node217 =
    Integer.Sparse.merge node215 node216 := by decide +kernel

theorem node217_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node217 x = ((((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) + (((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x)) := by
  rw [node217_check, Integer.Sparse.eval_merge]
  rw [node215_eval, node216_eval]

theorem node218_check : node218 =
    Integer.Sparse.merge node214 node217 := by decide +kernel

theorem node218_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node218 x = ((((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((20205267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + ((((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) + (((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x))) := by
  rw [node218_check, Integer.Sparse.eval_merge]
  rw [node214_eval, node217_eval]

theorem node219_check : node219 =
    Integer.Sparse.merge node212 node218 := by decide +kernel

theorem node219_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node219 x = (((((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) + ((((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((20205267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + ((((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) + (((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x)))) := by
  rw [node219_check, Integer.Sparse.eval_merge]
  rw [node212_eval, node218_eval]

theorem node220_check : node220 =
    Integer.Sparse.merge (Integer.Sparse.scale (2295640) entry_8_14) (Integer.Sparse.scale (13833571) entry_8_15) := by decide +kernel

theorem node220_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node220 x = (((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x) := by
  rw [node220_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node221_check : node221 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3579665) entry_8_13) node220 := by decide +kernel

theorem node221_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node221 x = (((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x)) := by
  rw [node221_check, Integer.Sparse.eval_merge]
  rw [node220_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node222_check : node222 =
    Integer.Sparse.merge (Integer.Sparse.scale (730101) entry_8_16) (Integer.Sparse.scale (6141615) entry_8_17) := by decide +kernel

theorem node222_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node222 x = (((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x) := by
  rw [node222_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node223_check : node223 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9345834) entry_8_18) (Integer.Sparse.scale (-1057876) entry_8_19) := by decide +kernel

theorem node223_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node223 x = (((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x) := by
  rw [node223_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node224_check : node224 =
    Integer.Sparse.merge node222 node223 := by decide +kernel

theorem node224_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node224 x = ((((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x) + (((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x)) := by
  rw [node224_check, Integer.Sparse.eval_merge]
  rw [node222_eval, node223_eval]

theorem node225_check : node225 =
    Integer.Sparse.merge node221 node224 := by decide +kernel

theorem node225_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node225 x = ((((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x)) + ((((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x) + (((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x))) := by
  rw [node225_check, Integer.Sparse.eval_merge]
  rw [node221_eval, node224_eval]

theorem node226_check : node226 =
    Integer.Sparse.merge (Integer.Sparse.scale (11010772) entry_8_21) (Integer.Sparse.scale (7616015) entry_8_22) := by decide +kernel

theorem node226_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node226 x = (((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_22 x) := by
  rw [node226_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node227_check : node227 =
    Integer.Sparse.merge (Integer.Sparse.scale (-83947) entry_8_20) node226 := by decide +kernel

theorem node227_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node227 x = (((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + (((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_22 x)) := by
  rw [node227_check, Integer.Sparse.eval_merge]
  rw [node226_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node228_check : node228 =
    Integer.Sparse.merge (Integer.Sparse.scale (5283323) entry_8_23) (Integer.Sparse.scale (2916394) entry_8_24) := by decide +kernel

theorem node228_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node228 x = (((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_23 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_24 x) := by
  rw [node228_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node229_check : node229 =
    Integer.Sparse.merge (Integer.Sparse.scale (-10448615) entry_8_25) (Integer.Sparse.scale (-3097019) entry_8_26) := by decide +kernel

theorem node229_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node229 x = (((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_25 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_26 x) := by
  rw [node229_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node230_check : node230 =
    Integer.Sparse.merge node228 node229 := by decide +kernel

theorem node230_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node230 x = ((((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_23 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_24 x) + (((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_25 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_26 x)) := by
  rw [node230_check, Integer.Sparse.eval_merge]
  rw [node228_eval, node229_eval]

theorem node231_check : node231 =
    Integer.Sparse.merge node227 node230 := by decide +kernel

theorem node231_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node231 x = ((((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + (((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_22 x)) + ((((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_23 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_24 x) + (((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_25 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_26 x))) := by
  rw [node231_check, Integer.Sparse.eval_merge]
  rw [node227_eval, node230_eval]

theorem node232_check : node232 =
    Integer.Sparse.merge node225 node231 := by decide +kernel

theorem node232_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node232 x = (((((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x)) + ((((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x) + (((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x))) + ((((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + (((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_22 x)) + ((((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_23 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_24 x) + (((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_25 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_26 x)))) := by
  rw [node232_check, Integer.Sparse.eval_merge]
  rw [node225_eval, node231_eval]

theorem node233_check : node233 =
    Integer.Sparse.merge node219 node232 := by decide +kernel

theorem node233_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node233 x = ((((((8323724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((7215886 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) + ((((3004866 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((-7671834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((20205267 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + ((((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + ((909816 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x) + (((2492242 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x + ((4317945 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_12 x)))) + (((((-3579665 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_13 x + (((2295640 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_14 x + ((13833571 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_15 x)) + ((((730101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_16 x + ((6141615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_17 x) + (((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_18 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_19 x))) + ((((-83947 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_20 x + (((11010772 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_21 x + ((7616015 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_22 x)) + ((((5283323 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_23 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_24 x) + (((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_25 x + ((-3097019 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_26 x))))) := by
  rw [node233_check, Integer.Sparse.eval_merge]
  rw [node219_eval, node232_eval]

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

theorem row_eval_8_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node233 x =
      ∑ j : Fin 27, (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x := by
  rw [node233_eval]
  exact (sum_expand_27 (fun j => (weights 8 j : ℝ) * Integer.Sparse.eval (entries 8 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_8_e_oai
