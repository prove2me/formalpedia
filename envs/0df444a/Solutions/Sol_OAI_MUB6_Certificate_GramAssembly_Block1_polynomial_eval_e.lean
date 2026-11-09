-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T12:17:40.444133+00:00
-- url     : https://prove2.me/submissions/e88d2d8b-08ff-46d7-b984-a6707a8ad21a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E001
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E196
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_rows_eval_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node420_check : node420 =
    Integer.Sparse.merge node19 node39 := by decide +kernel

theorem node420_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node420 x = (Integer.Sparse.eval node19 x + Integer.Sparse.eval node39 x) := by
  rw [node420_check, Integer.Sparse.eval_merge]

theorem node421_check : node421 =
    Integer.Sparse.merge node79 node99 := by decide +kernel

theorem node421_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node421 x = (Integer.Sparse.eval node79 x + Integer.Sparse.eval node99 x) := by
  rw [node421_check, Integer.Sparse.eval_merge]

theorem node422_check : node422 =
    Integer.Sparse.merge node59 node421 := by decide +kernel

theorem node422_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node422 x = (Integer.Sparse.eval node59 x + (Integer.Sparse.eval node79 x + Integer.Sparse.eval node99 x)) := by
  rw [node422_check, Integer.Sparse.eval_merge]
  rw [node421_eval]

theorem node423_check : node423 =
    Integer.Sparse.merge node420 node422 := by decide +kernel

theorem node423_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node423 x = ((Integer.Sparse.eval node19 x + Integer.Sparse.eval node39 x) + (Integer.Sparse.eval node59 x + (Integer.Sparse.eval node79 x + Integer.Sparse.eval node99 x))) := by
  rw [node423_check, Integer.Sparse.eval_merge]
  rw [node420_eval, node422_eval]

theorem node424_check : node424 =
    Integer.Sparse.merge node119 node139 := by decide +kernel

theorem node424_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node424 x = (Integer.Sparse.eval node119 x + Integer.Sparse.eval node139 x) := by
  rw [node424_check, Integer.Sparse.eval_merge]

theorem node425_check : node425 =
    Integer.Sparse.merge node179 node199 := by decide +kernel

theorem node425_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node425 x = (Integer.Sparse.eval node179 x + Integer.Sparse.eval node199 x) := by
  rw [node425_check, Integer.Sparse.eval_merge]

theorem node426_check : node426 =
    Integer.Sparse.merge node159 node425 := by decide +kernel

theorem node426_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node426 x = (Integer.Sparse.eval node159 x + (Integer.Sparse.eval node179 x + Integer.Sparse.eval node199 x)) := by
  rw [node426_check, Integer.Sparse.eval_merge]
  rw [node425_eval]

theorem node427_check : node427 =
    Integer.Sparse.merge node424 node426 := by decide +kernel

theorem node427_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node427 x = ((Integer.Sparse.eval node119 x + Integer.Sparse.eval node139 x) + (Integer.Sparse.eval node159 x + (Integer.Sparse.eval node179 x + Integer.Sparse.eval node199 x))) := by
  rw [node427_check, Integer.Sparse.eval_merge]
  rw [node424_eval, node426_eval]

theorem node428_check : node428 =
    Integer.Sparse.merge node423 node427 := by decide +kernel

theorem node428_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node428 x = (((Integer.Sparse.eval node19 x + Integer.Sparse.eval node39 x) + (Integer.Sparse.eval node59 x + (Integer.Sparse.eval node79 x + Integer.Sparse.eval node99 x))) + ((Integer.Sparse.eval node119 x + Integer.Sparse.eval node139 x) + (Integer.Sparse.eval node159 x + (Integer.Sparse.eval node179 x + Integer.Sparse.eval node199 x)))) := by
  rw [node428_check, Integer.Sparse.eval_merge]
  rw [node423_eval, node427_eval]

theorem node429_check : node429 =
    Integer.Sparse.merge node219 node239 := by decide +kernel

theorem node429_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node429 x = (Integer.Sparse.eval node219 x + Integer.Sparse.eval node239 x) := by
  rw [node429_check, Integer.Sparse.eval_merge]

theorem node430_check : node430 =
    Integer.Sparse.merge node279 node299 := by decide +kernel

theorem node430_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node430 x = (Integer.Sparse.eval node279 x + Integer.Sparse.eval node299 x) := by
  rw [node430_check, Integer.Sparse.eval_merge]

theorem node431_check : node431 =
    Integer.Sparse.merge node259 node430 := by decide +kernel

theorem node431_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node431 x = (Integer.Sparse.eval node259 x + (Integer.Sparse.eval node279 x + Integer.Sparse.eval node299 x)) := by
  rw [node431_check, Integer.Sparse.eval_merge]
  rw [node430_eval]

theorem node432_check : node432 =
    Integer.Sparse.merge node429 node431 := by decide +kernel

theorem node432_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node432 x = ((Integer.Sparse.eval node219 x + Integer.Sparse.eval node239 x) + (Integer.Sparse.eval node259 x + (Integer.Sparse.eval node279 x + Integer.Sparse.eval node299 x))) := by
  rw [node432_check, Integer.Sparse.eval_merge]
  rw [node429_eval, node431_eval]

theorem node433_check : node433 =
    Integer.Sparse.merge node339 node359 := by decide +kernel

theorem node433_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node433 x = (Integer.Sparse.eval node339 x + Integer.Sparse.eval node359 x) := by
  rw [node433_check, Integer.Sparse.eval_merge]

theorem node434_check : node434 =
    Integer.Sparse.merge node319 node433 := by decide +kernel

theorem node434_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node434 x = (Integer.Sparse.eval node319 x + (Integer.Sparse.eval node339 x + Integer.Sparse.eval node359 x)) := by
  rw [node434_check, Integer.Sparse.eval_merge]
  rw [node433_eval]

theorem node435_check : node435 =
    Integer.Sparse.merge node399 node419 := by decide +kernel

theorem node435_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node435 x = (Integer.Sparse.eval node399 x + Integer.Sparse.eval node419 x) := by
  rw [node435_check, Integer.Sparse.eval_merge]

theorem node436_check : node436 =
    Integer.Sparse.merge node379 node435 := by decide +kernel

theorem node436_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node436 x = (Integer.Sparse.eval node379 x + (Integer.Sparse.eval node399 x + Integer.Sparse.eval node419 x)) := by
  rw [node436_check, Integer.Sparse.eval_merge]
  rw [node435_eval]

theorem node437_check : node437 =
    Integer.Sparse.merge node434 node436 := by decide +kernel

theorem node437_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node437 x = ((Integer.Sparse.eval node319 x + (Integer.Sparse.eval node339 x + Integer.Sparse.eval node359 x)) + (Integer.Sparse.eval node379 x + (Integer.Sparse.eval node399 x + Integer.Sparse.eval node419 x))) := by
  rw [node437_check, Integer.Sparse.eval_merge]
  rw [node434_eval, node436_eval]

theorem node438_check : node438 =
    Integer.Sparse.merge node432 node437 := by decide +kernel

theorem node438_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node438 x = (((Integer.Sparse.eval node219 x + Integer.Sparse.eval node239 x) + (Integer.Sparse.eval node259 x + (Integer.Sparse.eval node279 x + Integer.Sparse.eval node299 x))) + ((Integer.Sparse.eval node319 x + (Integer.Sparse.eval node339 x + Integer.Sparse.eval node359 x)) + (Integer.Sparse.eval node379 x + (Integer.Sparse.eval node399 x + Integer.Sparse.eval node419 x)))) := by
  rw [node438_check, Integer.Sparse.eval_merge]
  rw [node432_eval, node437_eval]

theorem node439_check : node439 =
    Integer.Sparse.merge node428 node438 := by decide +kernel

theorem node439_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node439 x = ((((Integer.Sparse.eval node19 x + Integer.Sparse.eval node39 x) + (Integer.Sparse.eval node59 x + (Integer.Sparse.eval node79 x + Integer.Sparse.eval node99 x))) + ((Integer.Sparse.eval node119 x + Integer.Sparse.eval node139 x) + (Integer.Sparse.eval node159 x + (Integer.Sparse.eval node179 x + Integer.Sparse.eval node199 x)))) + (((Integer.Sparse.eval node219 x + Integer.Sparse.eval node239 x) + (Integer.Sparse.eval node259 x + (Integer.Sparse.eval node279 x + Integer.Sparse.eval node299 x))) + ((Integer.Sparse.eval node319 x + (Integer.Sparse.eval node339 x + Integer.Sparse.eval node359 x)) + (Integer.Sparse.eval node379 x + (Integer.Sparse.eval node399 x + Integer.Sparse.eval node419 x))))) := by
  rw [node439_check, Integer.Sparse.eval_merge]
  rw [node428_eval, node438_eval]

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

theorem polynomial_eval_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 21, ∑ j : Fin 21, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 21, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node439_eval]
      exact (sum_expand_21 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval_e]

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_eval_e_oai
