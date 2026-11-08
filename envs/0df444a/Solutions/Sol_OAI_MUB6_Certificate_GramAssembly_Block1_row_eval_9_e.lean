-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:36.573406+00:00
-- url     : https://prove2.me/submissions/1ee12edf-8167-43fd-a10a-41665dd9e6c1

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node180_check : node180 =
    Integer.Sparse.merge (Integer.Sparse.scale (-6253927) entry_9_0) (Integer.Sparse.scale (-1175469) entry_9_1) := by decide +kernel

theorem node180_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node180 x = (((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) := by
  rw [node180_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node181_check : node181 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1057177) entry_9_3) (Integer.Sparse.scale (263008) entry_9_4) := by decide +kernel

theorem node181_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node181 x = (((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x) := by
  rw [node181_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node182_check : node182 =
    Integer.Sparse.merge (Integer.Sparse.scale (-425014) entry_9_2) node181 := by decide +kernel

theorem node182_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node182 x = (((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x)) := by
  rw [node182_check, Integer.Sparse.eval_merge]
  rw [node181_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node183_check : node183 =
    Integer.Sparse.merge node180 node182 := by decide +kernel

theorem node183_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node183 x = ((((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) := by
  rw [node183_check, Integer.Sparse.eval_merge]
  rw [node180_eval, node182_eval]

theorem node184_check : node184 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3017686) entry_9_5) (Integer.Sparse.scale (1793037) entry_9_6) := by decide +kernel

theorem node184_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node184 x = (((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x) := by
  rw [node184_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node185_check : node185 =
    Integer.Sparse.merge (Integer.Sparse.scale (419757) entry_9_8) (Integer.Sparse.scale (16546248) entry_9_9) := by decide +kernel

theorem node185_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node185 x = (((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + ((16546248 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x) := by
  rw [node185_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node186_check : node186 =
    Integer.Sparse.merge (Integer.Sparse.scale (1053902) entry_9_7) node185 := by decide +kernel

theorem node186_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node186 x = (((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + (((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + ((16546248 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x)) := by
  rw [node186_check, Integer.Sparse.eval_merge]
  rw [node185_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node187_check : node187 =
    Integer.Sparse.merge node184 node186 := by decide +kernel

theorem node187_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node187 x = ((((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x) + (((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + (((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + ((16546248 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x))) := by
  rw [node187_check, Integer.Sparse.eval_merge]
  rw [node184_eval, node186_eval]

theorem node188_check : node188 =
    Integer.Sparse.merge node183 node187 := by decide +kernel

theorem node188_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node188 x = (((((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) + ((((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x) + (((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + (((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + ((16546248 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x)))) := by
  rw [node188_check, Integer.Sparse.eval_merge]
  rw [node183_eval, node187_eval]

theorem node189_check : node189 =
    Integer.Sparse.merge (Integer.Sparse.scale (681453) entry_9_10) (Integer.Sparse.scale (-488773) entry_9_11) := by decide +kernel

theorem node189_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node189 x = (((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x) := by
  rw [node189_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node190_check : node190 =
    Integer.Sparse.merge (Integer.Sparse.scale (1241050) entry_9_13) (Integer.Sparse.scale (2081231) entry_9_14) := by decide +kernel

theorem node190_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node190 x = (((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x) := by
  rw [node190_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node191_check : node191 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9664796) entry_9_12) node190 := by decide +kernel

theorem node191_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node191 x = (((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x + (((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x)) := by
  rw [node191_check, Integer.Sparse.eval_merge]
  rw [node190_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node192_check : node192 =
    Integer.Sparse.merge node189 node191 := by decide +kernel

theorem node192_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node192 x = ((((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x) + (((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x + (((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x))) := by
  rw [node192_check, Integer.Sparse.eval_merge]
  rw [node189_eval, node191_eval]

theorem node193_check : node193 =
    Integer.Sparse.merge (Integer.Sparse.scale (11353138) entry_9_16) (Integer.Sparse.scale (-1846105) entry_9_17) := by decide +kernel

theorem node193_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node193 x = (((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x) := by
  rw [node193_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node194_check : node194 =
    Integer.Sparse.merge (Integer.Sparse.scale (2667867) entry_9_15) node193 := by decide +kernel

theorem node194_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node194 x = (((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x + (((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x)) := by
  rw [node194_check, Integer.Sparse.eval_merge]
  rw [node193_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node195_check : node195 =
    Integer.Sparse.merge (Integer.Sparse.scale (1567125) entry_9_19) (Integer.Sparse.scale (10741408) entry_9_20) := by decide +kernel

theorem node195_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node195 x = (((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x) := by
  rw [node195_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node196_check : node196 =
    Integer.Sparse.merge (Integer.Sparse.scale (4400021) entry_9_18) node195 := by decide +kernel

theorem node196_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node196 x = (((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + (((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x)) := by
  rw [node196_check, Integer.Sparse.eval_merge]
  rw [node195_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node197_check : node197 =
    Integer.Sparse.merge node194 node196 := by decide +kernel

theorem node197_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node197 x = ((((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x + (((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x)) + (((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + (((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x))) := by
  rw [node197_check, Integer.Sparse.eval_merge]
  rw [node194_eval, node196_eval]

theorem node198_check : node198 =
    Integer.Sparse.merge node192 node197 := by decide +kernel

theorem node198_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node198 x = (((((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x) + (((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x + (((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x))) + ((((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x + (((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x)) + (((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + (((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x)))) := by
  rw [node198_check, Integer.Sparse.eval_merge]
  rw [node192_eval, node197_eval]

theorem node199_check : node199 =
    Integer.Sparse.merge node188 node198 := by decide +kernel

theorem node199_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node199 x = ((((((-6253927 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + ((-1175469 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x) + (((-425014 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x + (((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x))) + ((((-3017686 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x + ((1793037 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x) + (((1053902 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + (((419757 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x + ((16546248 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x)))) + (((((681453 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((-488773 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x) + (((-9664796 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_12 x + (((1241050 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_13 x + ((2081231 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_14 x))) + ((((2667867 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_15 x + (((11353138 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_16 x + ((-1846105 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_17 x)) + (((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_18 x + (((1567125 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_19 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_20 x))))) := by
  rw [node199_check, Integer.Sparse.eval_merge]
  rw [node188_eval, node198_eval]

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

theorem row_eval_9_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node199 x =
      ∑ j : Fin 21, (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x := by
  rw [node199_eval]
  exact (sum_expand_21 (fun j => (weights 9 j : ℝ) * Integer.Sparse.eval (entries 9 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_9_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_9_e_oai
