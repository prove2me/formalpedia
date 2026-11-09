-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:37:14.315672+00:00
-- url     : https://prove2.me/submissions/27db96e5-a2c8-4da7-8b1e-1a3608d1f2aa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E176
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node234_check : node234 =
    Integer.Sparse.merge (Integer.Sparse.scale (337531) entry_9_1) (Integer.Sparse.scale (-216243) entry_9_2) := by decide +kernel

theorem node234_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node234 x = (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x) := by
  rw [node234_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node235_check : node235 =
    Integer.Sparse.merge (Integer.Sparse.scale (7441570) entry_9_0) node234 := by decide +kernel

theorem node235_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node235 x = (((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) := by
  rw [node235_check, Integer.Sparse.eval_merge]
  rw [node234_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node236_check : node236 =
    Integer.Sparse.merge (Integer.Sparse.scale (5805250) entry_9_4) (Integer.Sparse.scale (-3927318) entry_9_5) := by decide +kernel

theorem node236_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node236 x = (((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x) := by
  rw [node236_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node237_check : node237 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3526786) entry_9_3) node236 := by decide +kernel

theorem node237_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node237 x = (((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x)) := by
  rw [node237_check, Integer.Sparse.eval_merge]
  rw [node236_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node238_check : node238 =
    Integer.Sparse.merge node235 node237 := by decide +kernel

theorem node238_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node238 x = ((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) := by
  rw [node238_check, Integer.Sparse.eval_merge]
  rw [node235_eval, node237_eval]

theorem node239_check : node239 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6735967) entry_9_7) (Integer.Sparse.scale (10681732) entry_9_8) := by decide +kernel

theorem node239_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node239 x = (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x) := by
  rw [node239_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node240_check : node240 =
    Integer.Sparse.merge (Integer.Sparse.scale (1839889) entry_9_6) node239 := by decide +kernel

theorem node240_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node240 x = (((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) := by
  rw [node240_check, Integer.Sparse.eval_merge]
  rw [node239_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node241_check : node241 =
    Integer.Sparse.merge (Integer.Sparse.scale (16547778) entry_9_9) (Integer.Sparse.scale (-2924799) entry_9_10) := by decide +kernel

theorem node241_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node241 x = (((16547778 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) := by
  rw [node241_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node242_check : node242 =
    Integer.Sparse.merge (Integer.Sparse.scale (3946206) entry_9_11) (Integer.Sparse.scale (5011875) entry_9_12) := by decide +kernel

theorem node242_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node242 x = (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x) := by
  rw [node242_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node243_check : node243 =
    Integer.Sparse.merge node241 node242 := by decide +kernel

theorem node243_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node243 x = ((((16547778 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) + (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x)) := by
  rw [node243_check, Integer.Sparse.eval_merge]
  rw [node241_eval, node242_eval]

theorem node244_check : node244 =
    Integer.Sparse.merge node240 node243 := by decide +kernel

theorem node244_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node244 x = ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + ((((16547778 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) + (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x))) := by
  rw [node244_check, Integer.Sparse.eval_merge]
  rw [node240_eval, node243_eval]

theorem node245_check : node245 =
    Integer.Sparse.merge node238 node244 := by decide +kernel

theorem node245_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node245 x = (((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + ((((16547778 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) + (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x)))) := by
  rw [node245_check, Integer.Sparse.eval_merge]
  rw [node238_eval, node244_eval]

theorem node246_check : node246 =
    Integer.Sparse.merge (Integer.Sparse.scale (1384567) entry_9_14) (Integer.Sparse.scale (12642667) entry_9_15) := by decide +kernel

theorem node246_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node246 x = (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x) := by
  rw [node246_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node247_check : node247 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2276717) entry_9_13) node246 := by decide +kernel

theorem node247_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node247 x = (((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x)) := by
  rw [node247_check, Integer.Sparse.eval_merge]
  rw [node246_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node248_check : node248 =
    Integer.Sparse.merge (Integer.Sparse.scale (479639) entry_9_16) (Integer.Sparse.scale (12059339) entry_9_17) := by decide +kernel

theorem node248_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node248 x = (((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x) := by
  rw [node248_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node249_check : node249 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4897979) entry_9_18) (Integer.Sparse.scale (-9757133) entry_9_19) := by decide +kernel

theorem node249_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node249 x = (((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + ((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x) := by
  rw [node249_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node250_check : node250 =
    Integer.Sparse.merge node248 node249 := by decide +kernel

theorem node250_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node250 x = ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x) + (((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + ((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x)) := by
  rw [node250_check, Integer.Sparse.eval_merge]
  rw [node248_eval, node249_eval]

theorem node251_check : node251 =
    Integer.Sparse.merge node247 node250 := by decide +kernel

theorem node251_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node251 x = ((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x)) + ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x) + (((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + ((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x))) := by
  rw [node251_check, Integer.Sparse.eval_merge]
  rw [node247_eval, node250_eval]

theorem node252_check : node252 =
    Integer.Sparse.merge (Integer.Sparse.scale (4755447) entry_9_21) (Integer.Sparse.scale (-1246459) entry_9_22) := by decide +kernel

theorem node252_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node252 x = (((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x + ((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_22 x) := by
  rw [node252_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node253_check : node253 =
    Integer.Sparse.merge (Integer.Sparse.scale (-304344) entry_9_20) node252 := by decide +kernel

theorem node253_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node253 x = (((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + (((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x + ((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_22 x)) := by
  rw [node253_check, Integer.Sparse.eval_merge]
  rw [node252_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node254_check : node254 =
    Integer.Sparse.merge (Integer.Sparse.scale (4687144) entry_9_23) (Integer.Sparse.scale (2310344) entry_9_24) := by decide +kernel

theorem node254_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node254 x = (((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_23 x + ((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_24 x) := by
  rw [node254_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node255_check : node255 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1413894) entry_9_25) (Integer.Sparse.scale (-2054950) entry_9_26) := by decide +kernel

theorem node255_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node255 x = (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_25 x + ((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_26 x) := by
  rw [node255_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node256_check : node256 =
    Integer.Sparse.merge node254 node255 := by decide +kernel

theorem node256_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node256 x = ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_23 x + ((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_24 x) + (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_25 x + ((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_26 x)) := by
  rw [node256_check, Integer.Sparse.eval_merge]
  rw [node254_eval, node255_eval]

theorem node257_check : node257 =
    Integer.Sparse.merge node253 node256 := by decide +kernel

theorem node257_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node257 x = ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + (((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x + ((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_22 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_23 x + ((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_24 x) + (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_25 x + ((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_26 x))) := by
  rw [node257_check, Integer.Sparse.eval_merge]
  rw [node253_eval, node256_eval]

theorem node258_check : node258 =
    Integer.Sparse.merge node251 node257 := by decide +kernel

theorem node258_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node258 x = (((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x)) + ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x) + (((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + ((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x))) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + (((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x + ((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_22 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_23 x + ((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_24 x) + (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_25 x + ((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_26 x)))) := by
  rw [node258_check, Integer.Sparse.eval_merge]
  rw [node251_eval, node257_eval]

theorem node259_check : node259 =
    Integer.Sparse.merge node245 node258 := by decide +kernel

theorem node259_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x = ((((((7441570 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((5805250 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) + ((((1839889 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((-6735967 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((10681732 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + ((((16547778 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + ((-2924799 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x) + (((3946206 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x + ((5011875 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x)))) + (((((-2276717 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + (((1384567 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x + ((12642667 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x)) + ((((479639 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((12059339 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x) + (((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + ((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x))) + ((((-304344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x + (((4755447 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_21 x + ((-1246459 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_22 x)) + ((((4687144 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_23 x + ((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_24 x) + (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_25 x + ((-2054950 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_26 x))))) := by
  rw [node259_check, Integer.Sparse.eval_merge]
  rw [node245_eval, node258_eval]

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

theorem row_eval_9_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node259 x =
      ∑ j : Fin 27, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node259_eval]
  exact (sum_expand_27 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_9_e_oai
