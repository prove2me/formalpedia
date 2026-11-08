-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:22.874193+00:00
-- url     : https://prove2.me/submissions/b69010dd-0200-4480-acaf-2fe6b1bc4b56

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node360_check : node360 =
    Integer.Sparse.merge (Integer.Sparse.scale (2313302) entry_18_0) (Integer.Sparse.scale (-1529579) entry_18_1) := by decide +kernel

theorem node360_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node360 x = (((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) := by
  rw [node360_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node361_check : node361 =
    Integer.Sparse.merge (Integer.Sparse.scale (300878) entry_18_3) (Integer.Sparse.scale (-4308765) entry_18_4) := by decide +kernel

theorem node361_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node361 x = (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x) := by
  rw [node361_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node362_check : node362 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1719750) entry_18_2) node361 := by decide +kernel

theorem node362_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node362 x = (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x)) := by
  rw [node362_check, Integer.Sparse.eval_merge]
  rw [node361_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node363_check : node363 =
    Integer.Sparse.merge node360 node362 := by decide +kernel

theorem node363_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node363 x = ((((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) := by
  rw [node363_check, Integer.Sparse.eval_merge]
  rw [node360_eval, node362_eval]

theorem node364_check : node364 =
    Integer.Sparse.merge (Integer.Sparse.scale (250358) entry_18_5) (Integer.Sparse.scale (5095570) entry_18_6) := by decide +kernel

theorem node364_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node364 x = (((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + ((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x) := by
  rw [node364_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node365_check : node365 =
    Integer.Sparse.merge (Integer.Sparse.scale (1306896) entry_18_8) (Integer.Sparse.scale (4400021) entry_18_9) := by decide +kernel

theorem node365_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node365 x = (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + ((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x) := by
  rw [node365_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node366_check : node366 =
    Integer.Sparse.merge (Integer.Sparse.scale (201825) entry_18_7) node365 := by decide +kernel

theorem node366_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node366 x = (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + ((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x)) := by
  rw [node366_check, Integer.Sparse.eval_merge]
  rw [node365_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node367_check : node367 =
    Integer.Sparse.merge node364 node366 := by decide +kernel

theorem node367_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node367 x = ((((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + ((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x) + (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + ((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x))) := by
  rw [node367_check, Integer.Sparse.eval_merge]
  rw [node364_eval, node366_eval]

theorem node368_check : node368 =
    Integer.Sparse.merge node363 node367 := by decide +kernel

theorem node368_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node368 x = (((((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) + ((((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + ((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x) + (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + ((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x)))) := by
  rw [node368_check, Integer.Sparse.eval_merge]
  rw [node363_eval, node367_eval]

theorem node369_check : node369 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1981023) entry_18_10) (Integer.Sparse.scale (-2418328) entry_18_11) := by decide +kernel

theorem node369_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node369 x = (((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x + ((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x) := by
  rw [node369_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node370_check : node370 =
    Integer.Sparse.merge (Integer.Sparse.scale (-760335) entry_18_13) (Integer.Sparse.scale (-4161086) entry_18_14) := by decide +kernel

theorem node370_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node370 x = (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + ((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x) := by
  rw [node370_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node371_check : node371 =
    Integer.Sparse.merge (Integer.Sparse.scale (-23030655) entry_18_12) node370 := by decide +kernel

theorem node371_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node371 x = (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + ((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x)) := by
  rw [node371_check, Integer.Sparse.eval_merge]
  rw [node370_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node372_check : node372 =
    Integer.Sparse.merge node369 node371 := by decide +kernel

theorem node372_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node372 x = ((((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x + ((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x) + (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + ((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x))) := by
  rw [node372_check, Integer.Sparse.eval_merge]
  rw [node369_eval, node371_eval]

theorem node373_check : node373 =
    Integer.Sparse.merge (Integer.Sparse.scale (10606059) entry_18_16) (Integer.Sparse.scale (1990541) entry_18_17) := by decide +kernel

theorem node373_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node373 x = (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) := by
  rw [node373_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node374_check : node374 =
    Integer.Sparse.merge (Integer.Sparse.scale (12375243) entry_18_15) node373 := by decide +kernel

theorem node374_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node374 x = (((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x)) := by
  rw [node374_check, Integer.Sparse.eval_merge]
  rw [node373_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node375_check : node375 =
    Integer.Sparse.merge (Integer.Sparse.scale (2123881) entry_18_19) (Integer.Sparse.scale (5457071) entry_18_20) := by decide +kernel

theorem node375_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node375 x = (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + ((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x) := by
  rw [node375_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node376_check : node376 =
    Integer.Sparse.merge (Integer.Sparse.scale (22638314) entry_18_18) node375 := by decide +kernel

theorem node376_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node376 x = (((22638314 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + ((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x)) := by
  rw [node376_check, Integer.Sparse.eval_merge]
  rw [node375_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node377_check : node377 =
    Integer.Sparse.merge node374 node376 := by decide +kernel

theorem node377_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node377 x = ((((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x)) + (((22638314 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + ((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x))) := by
  rw [node377_check, Integer.Sparse.eval_merge]
  rw [node374_eval, node376_eval]

theorem node378_check : node378 =
    Integer.Sparse.merge node372 node377 := by decide +kernel

theorem node378_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node378 x = (((((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x + ((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x) + (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + ((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x))) + ((((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x)) + (((22638314 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + ((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x)))) := by
  rw [node378_check, Integer.Sparse.eval_merge]
  rw [node372_eval, node377_eval]

theorem node379_check : node379 =
    Integer.Sparse.merge node368 node378 := by decide +kernel

theorem node379_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node379 x = ((((((2313302 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + ((-1529579 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x) + (((-1719750 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + ((-4308765 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x))) + ((((250358 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x + ((5095570 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x) + (((201825 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + (((1306896 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x + ((4400021 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x)))) + (((((-1981023 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x + ((-2418328 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x) + (((-23030655 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x + (((-760335 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + ((-4161086 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x))) + ((((12375243 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x + (((10606059 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((1990541 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x)) + (((22638314 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + (((2123881 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x + ((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x))))) := by
  rw [node379_check, Integer.Sparse.eval_merge]
  rw [node368_eval, node378_eval]

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

theorem row_eval_18_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node379 x =
      ∑ j : Fin 21, (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x := by
  rw [node379_eval]
  exact (sum_expand_21 (fun j => (weights 18 j : ℝ) * Integer.Sparse.eval (entries 18 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_18_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_18_e_oai
