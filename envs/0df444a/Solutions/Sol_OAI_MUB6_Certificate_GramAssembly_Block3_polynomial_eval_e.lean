-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:43:57.762416+00:00
-- url     : https://prove2.me/submissions/bc2e4d52-ec7c-4d61-a89a-715d9758f879

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E005
import Definitions.Def_OAIQ106E008
import Definitions.Def_OAIQ106E009
import Definitions.Def_OAIQ106E196
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_rows_eval_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node702_check : node702 =
    Integer.Sparse.merge node51 node77 := by decide +kernel

theorem node702_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node702 x = (Integer.Sparse.eval node51 x + Integer.Sparse.eval node77 x) := by
  rw [node702_check, Integer.Sparse.eval_merge]

theorem node703_check : node703 =
    Integer.Sparse.merge node25 node702 := by decide +kernel

theorem node703_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node703 x = (Integer.Sparse.eval node25 x + (Integer.Sparse.eval node51 x + Integer.Sparse.eval node77 x)) := by
  rw [node703_check, Integer.Sparse.eval_merge]
  rw [node702_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node704_check : node704 =
    Integer.Sparse.merge node129 node155 := by decide +kernel

theorem node704_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node704 x = (Integer.Sparse.eval node129 x + Integer.Sparse.eval node155 x) := by
  rw [node704_check, Integer.Sparse.eval_merge]

theorem node705_check : node705 =
    Integer.Sparse.merge node103 node704 := by decide +kernel

theorem node705_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node705 x = (Integer.Sparse.eval node103 x + (Integer.Sparse.eval node129 x + Integer.Sparse.eval node155 x)) := by
  rw [node705_check, Integer.Sparse.eval_merge]
  rw [node704_eval]

theorem node706_check : node706 =
    Integer.Sparse.merge node703 node705 := by decide +kernel

theorem node706_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node706 x = ((Integer.Sparse.eval node25 x + (Integer.Sparse.eval node51 x + Integer.Sparse.eval node77 x)) + (Integer.Sparse.eval node103 x + (Integer.Sparse.eval node129 x + Integer.Sparse.eval node155 x))) := by
  rw [node706_check, Integer.Sparse.eval_merge]
  rw [node703_eval, node705_eval]

theorem node707_check : node707 =
    Integer.Sparse.merge node207 node233 := by decide +kernel

theorem node707_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node707 x = (Integer.Sparse.eval node207 x + Integer.Sparse.eval node233 x) := by
  rw [node707_check, Integer.Sparse.eval_merge]

theorem node708_check : node708 =
    Integer.Sparse.merge node181 node707 := by decide +kernel

theorem node708_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node708 x = (Integer.Sparse.eval node181 x + (Integer.Sparse.eval node207 x + Integer.Sparse.eval node233 x)) := by
  rw [node708_check, Integer.Sparse.eval_merge]
  rw [node707_eval]

theorem node709_check : node709 =
    Integer.Sparse.merge node259 node285 := by decide +kernel

theorem node709_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node709 x = (Integer.Sparse.eval node259 x + Integer.Sparse.eval node285 x) := by
  rw [node709_check, Integer.Sparse.eval_merge]

theorem node710_check : node710 =
    Integer.Sparse.merge node311 node337 := by decide +kernel

theorem node710_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node710 x = (Integer.Sparse.eval node311 x + Integer.Sparse.eval node337 x) := by
  rw [node710_check, Integer.Sparse.eval_merge]

theorem node711_check : node711 =
    Integer.Sparse.merge node709 node710 := by decide +kernel

theorem node711_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node711 x = ((Integer.Sparse.eval node259 x + Integer.Sparse.eval node285 x) + (Integer.Sparse.eval node311 x + Integer.Sparse.eval node337 x)) := by
  rw [node711_check, Integer.Sparse.eval_merge]
  rw [node709_eval, node710_eval]

theorem node712_check : node712 =
    Integer.Sparse.merge node708 node711 := by decide +kernel

theorem node712_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node712 x = ((Integer.Sparse.eval node181 x + (Integer.Sparse.eval node207 x + Integer.Sparse.eval node233 x)) + ((Integer.Sparse.eval node259 x + Integer.Sparse.eval node285 x) + (Integer.Sparse.eval node311 x + Integer.Sparse.eval node337 x))) := by
  rw [node712_check, Integer.Sparse.eval_merge]
  rw [node708_eval, node711_eval]

theorem node713_check : node713 =
    Integer.Sparse.merge node706 node712 := by decide +kernel

theorem node713_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node713 x = (((Integer.Sparse.eval node25 x + (Integer.Sparse.eval node51 x + Integer.Sparse.eval node77 x)) + (Integer.Sparse.eval node103 x + (Integer.Sparse.eval node129 x + Integer.Sparse.eval node155 x))) + ((Integer.Sparse.eval node181 x + (Integer.Sparse.eval node207 x + Integer.Sparse.eval node233 x)) + ((Integer.Sparse.eval node259 x + Integer.Sparse.eval node285 x) + (Integer.Sparse.eval node311 x + Integer.Sparse.eval node337 x)))) := by
  rw [node713_check, Integer.Sparse.eval_merge]
  rw [node706_eval, node712_eval]

theorem node714_check : node714 =
    Integer.Sparse.merge node389 node415 := by decide +kernel

theorem node714_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node714 x = (Integer.Sparse.eval node389 x + Integer.Sparse.eval node415 x) := by
  rw [node714_check, Integer.Sparse.eval_merge]

theorem node715_check : node715 =
    Integer.Sparse.merge node363 node714 := by decide +kernel

theorem node715_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node715 x = (Integer.Sparse.eval node363 x + (Integer.Sparse.eval node389 x + Integer.Sparse.eval node415 x)) := by
  rw [node715_check, Integer.Sparse.eval_merge]
  rw [node714_eval]

theorem node716_check : node716 =
    Integer.Sparse.merge node441 node467 := by decide +kernel

theorem node716_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node716 x = (Integer.Sparse.eval node441 x + Integer.Sparse.eval node467 x) := by
  rw [node716_check, Integer.Sparse.eval_merge]

theorem node717_check : node717 =
    Integer.Sparse.merge node493 node519 := by decide +kernel

theorem node717_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node717 x = (Integer.Sparse.eval node493 x + Integer.Sparse.eval node519 x) := by
  rw [node717_check, Integer.Sparse.eval_merge]

theorem node718_check : node718 =
    Integer.Sparse.merge node716 node717 := by decide +kernel

theorem node718_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node718 x = ((Integer.Sparse.eval node441 x + Integer.Sparse.eval node467 x) + (Integer.Sparse.eval node493 x + Integer.Sparse.eval node519 x)) := by
  rw [node718_check, Integer.Sparse.eval_merge]
  rw [node716_eval, node717_eval]

theorem node719_check : node719 =
    Integer.Sparse.merge node715 node718 := by decide +kernel

theorem node719_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node719 x = ((Integer.Sparse.eval node363 x + (Integer.Sparse.eval node389 x + Integer.Sparse.eval node415 x)) + ((Integer.Sparse.eval node441 x + Integer.Sparse.eval node467 x) + (Integer.Sparse.eval node493 x + Integer.Sparse.eval node519 x))) := by
  rw [node719_check, Integer.Sparse.eval_merge]
  rw [node715_eval, node718_eval]

theorem node720_check : node720 =
    Integer.Sparse.merge node571 node597 := by decide +kernel

theorem node720_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node720 x = (Integer.Sparse.eval node571 x + Integer.Sparse.eval node597 x) := by
  rw [node720_check, Integer.Sparse.eval_merge]

theorem node721_check : node721 =
    Integer.Sparse.merge node545 node720 := by decide +kernel

theorem node721_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node721 x = (Integer.Sparse.eval node545 x + (Integer.Sparse.eval node571 x + Integer.Sparse.eval node597 x)) := by
  rw [node721_check, Integer.Sparse.eval_merge]
  rw [node720_eval]

theorem node722_check : node722 =
    Integer.Sparse.merge node623 node649 := by decide +kernel

theorem node722_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node722 x = (Integer.Sparse.eval node623 x + Integer.Sparse.eval node649 x) := by
  rw [node722_check, Integer.Sparse.eval_merge]

theorem node723_check : node723 =
    Integer.Sparse.merge node675 node701 := by decide +kernel

theorem node723_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node723 x = (Integer.Sparse.eval node675 x + Integer.Sparse.eval node701 x) := by
  rw [node723_check, Integer.Sparse.eval_merge]

theorem node724_check : node724 =
    Integer.Sparse.merge node722 node723 := by decide +kernel

theorem node724_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node724 x = ((Integer.Sparse.eval node623 x + Integer.Sparse.eval node649 x) + (Integer.Sparse.eval node675 x + Integer.Sparse.eval node701 x)) := by
  rw [node724_check, Integer.Sparse.eval_merge]
  rw [node722_eval, node723_eval]

theorem node725_check : node725 =
    Integer.Sparse.merge node721 node724 := by decide +kernel

theorem node725_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node725 x = ((Integer.Sparse.eval node545 x + (Integer.Sparse.eval node571 x + Integer.Sparse.eval node597 x)) + ((Integer.Sparse.eval node623 x + Integer.Sparse.eval node649 x) + (Integer.Sparse.eval node675 x + Integer.Sparse.eval node701 x))) := by
  rw [node725_check, Integer.Sparse.eval_merge]
  rw [node721_eval, node724_eval]

theorem node726_check : node726 =
    Integer.Sparse.merge node719 node725 := by decide +kernel

theorem node726_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node726 x = (((Integer.Sparse.eval node363 x + (Integer.Sparse.eval node389 x + Integer.Sparse.eval node415 x)) + ((Integer.Sparse.eval node441 x + Integer.Sparse.eval node467 x) + (Integer.Sparse.eval node493 x + Integer.Sparse.eval node519 x))) + ((Integer.Sparse.eval node545 x + (Integer.Sparse.eval node571 x + Integer.Sparse.eval node597 x)) + ((Integer.Sparse.eval node623 x + Integer.Sparse.eval node649 x) + (Integer.Sparse.eval node675 x + Integer.Sparse.eval node701 x)))) := by
  rw [node726_check, Integer.Sparse.eval_merge]
  rw [node719_eval, node725_eval]

theorem node727_check : node727 =
    Integer.Sparse.merge node713 node726 := by decide +kernel

theorem node727_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node727 x = ((((Integer.Sparse.eval node25 x + (Integer.Sparse.eval node51 x + Integer.Sparse.eval node77 x)) + (Integer.Sparse.eval node103 x + (Integer.Sparse.eval node129 x + Integer.Sparse.eval node155 x))) + ((Integer.Sparse.eval node181 x + (Integer.Sparse.eval node207 x + Integer.Sparse.eval node233 x)) + ((Integer.Sparse.eval node259 x + Integer.Sparse.eval node285 x) + (Integer.Sparse.eval node311 x + Integer.Sparse.eval node337 x)))) + (((Integer.Sparse.eval node363 x + (Integer.Sparse.eval node389 x + Integer.Sparse.eval node415 x)) + ((Integer.Sparse.eval node441 x + Integer.Sparse.eval node467 x) + (Integer.Sparse.eval node493 x + Integer.Sparse.eval node519 x))) + ((Integer.Sparse.eval node545 x + (Integer.Sparse.eval node571 x + Integer.Sparse.eval node597 x)) + ((Integer.Sparse.eval node623 x + Integer.Sparse.eval node649 x) + (Integer.Sparse.eval node675 x + Integer.Sparse.eval node701 x))))) := by
  rw [node727_check, Integer.Sparse.eval_merge]
  rw [node713_eval, node726_eval]

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

theorem polynomial_eval_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 27, ∑ j : Fin 27, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 27, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node727_eval]
      exact (sum_expand_27 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval_e]

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_eval_e_oai
