-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:27.366934+00:00
-- url     : https://prove2.me/submissions/d2325e1a-7ddc-4538-b075-875cf192cd56

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E173
import Definitions.Def_OAIQ106E174
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block1Part12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

theorem node400_check : node400 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8259767) entry_20_0) (Integer.Sparse.scale (-1803981) entry_20_1) := by decide +kernel

theorem node400_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node400 x = (((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) := by
  rw [node400_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node401_check : node401 =
    Integer.Sparse.merge (Integer.Sparse.scale (-720802) entry_20_3) (Integer.Sparse.scale (1327786) entry_20_4) := by decide +kernel

theorem node401_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node401 x = (((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x) := by
  rw [node401_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node402_check : node402 =
    Integer.Sparse.merge (Integer.Sparse.scale (2527166) entry_20_2) node401 := by decide +kernel

theorem node402_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node402 x = (((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x)) := by
  rw [node402_check, Integer.Sparse.eval_merge]
  rw [node401_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node403_check : node403 =
    Integer.Sparse.merge node400 node402 := by decide +kernel

theorem node403_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node403 x = ((((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) + (((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x))) := by
  rw [node403_check, Integer.Sparse.eval_merge]
  rw [node400_eval, node402_eval]

theorem node404_check : node404 =
    Integer.Sparse.merge (Integer.Sparse.scale (3409136) entry_20_5) (Integer.Sparse.scale (-299969) entry_20_6) := by decide +kernel

theorem node404_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node404 x = (((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x) := by
  rw [node404_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node405_check : node405 =
    Integer.Sparse.merge (Integer.Sparse.scale (660976) entry_20_8) (Integer.Sparse.scale (10741408) entry_20_9) := by decide +kernel

theorem node405_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node405 x = (((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x) := by
  rw [node405_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node406_check : node406 =
    Integer.Sparse.merge (Integer.Sparse.scale (1677944) entry_20_7) node405 := by decide +kernel

theorem node406_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node406 x = (((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + (((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x)) := by
  rw [node406_check, Integer.Sparse.eval_merge]
  rw [node405_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node407_check : node407 =
    Integer.Sparse.merge node404 node406 := by decide +kernel

theorem node407_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node407 x = ((((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x) + (((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + (((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x))) := by
  rw [node407_check, Integer.Sparse.eval_merge]
  rw [node404_eval, node406_eval]

theorem node408_check : node408 =
    Integer.Sparse.merge node403 node407 := by decide +kernel

theorem node408_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node408 x = (((((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) + (((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x))) + ((((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x) + (((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + (((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x)))) := by
  rw [node408_check, Integer.Sparse.eval_merge]
  rw [node403_eval, node407_eval]

theorem node409_check : node409 =
    Integer.Sparse.merge (Integer.Sparse.scale (1464376) entry_20_10) (Integer.Sparse.scale (905478) entry_20_11) := by decide +kernel

theorem node409_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node409 x = (((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x) := by
  rw [node409_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node410_check : node410 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1728565) entry_20_13) (Integer.Sparse.scale (4379858) entry_20_14) := by decide +kernel

theorem node410_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node410 x = (((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x) := by
  rw [node410_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node411_check : node411 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9593464) entry_20_12) node410 := by decide +kernel

theorem node411_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node411 x = (((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x + (((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x)) := by
  rw [node411_check, Integer.Sparse.eval_merge]
  rw [node410_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node412_check : node412 =
    Integer.Sparse.merge node409 node411 := by decide +kernel

theorem node412_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node412 x = ((((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x) + (((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x + (((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x))) := by
  rw [node412_check, Integer.Sparse.eval_merge]
  rw [node409_eval, node411_eval]

theorem node413_check : node413 =
    Integer.Sparse.merge (Integer.Sparse.scale (10905753) entry_20_16) (Integer.Sparse.scale (5534083) entry_20_17) := by decide +kernel

theorem node413_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node413 x = (((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x) := by
  rw [node413_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node414_check : node414 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1351879) entry_20_15) node413 := by decide +kernel

theorem node414_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node414 x = (((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x + (((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x)) := by
  rw [node414_check, Integer.Sparse.eval_merge]
  rw [node413_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node415_check : node415 =
    Integer.Sparse.merge (Integer.Sparse.scale (-963816) entry_20_19) (Integer.Sparse.scale (15446253) entry_20_20) := by decide +kernel

theorem node415_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node415 x = (((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + ((15446253 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x) := by
  rw [node415_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

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

theorem node416_check : node416 =
    Integer.Sparse.merge (Integer.Sparse.scale (5457071) entry_20_18) node415 := by decide +kernel

theorem node416_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node416 x = (((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + (((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + ((15446253 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x)) := by
  rw [node416_check, Integer.Sparse.eval_merge]
  rw [node415_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node417_check : node417 =
    Integer.Sparse.merge node414 node416 := by decide +kernel

theorem node417_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node417 x = ((((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x + (((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x)) + (((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + (((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + ((15446253 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x))) := by
  rw [node417_check, Integer.Sparse.eval_merge]
  rw [node414_eval, node416_eval]

theorem node418_check : node418 =
    Integer.Sparse.merge node412 node417 := by decide +kernel

theorem node418_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node418 x = (((((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x) + (((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x + (((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x))) + ((((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x + (((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x)) + (((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + (((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + ((15446253 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x)))) := by
  rw [node418_check, Integer.Sparse.eval_merge]
  rw [node412_eval, node417_eval]

theorem node419_check : node419 =
    Integer.Sparse.merge node408 node418 := by decide +kernel

theorem node419_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x = ((((((-8259767 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_0 x + ((-1803981 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_1 x) + (((2527166 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_2 x + (((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_3 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_4 x))) + ((((3409136 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_5 x + ((-299969 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_6 x) + (((1677944 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_7 x + (((660976 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_8 x + ((10741408 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_9 x)))) + (((((1464376 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_10 x + ((905478 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_11 x) + (((-9593464 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_12 x + (((-1728565 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_13 x + ((4379858 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_14 x))) + ((((-1351879 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_15 x + (((10905753 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_16 x + ((5534083 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_17 x)) + (((5457071 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_18 x + (((-963816 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_19 x + ((15446253 : ℤ) : ℝ) * Integer.Sparse.eval entry_20_20 x))))) := by
  rw [node419_check, Integer.Sparse.eval_merge]
  rw [node408_eval, node418_eval]

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

theorem row_eval_20_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node419 x =
      ∑ j : Fin 21, (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x := by
  rw [node419_eval]
  exact (sum_expand_21 (fun j => (weights 20 j : ℝ) * Integer.Sparse.eval (entries 20 j) x)).symm

end MUB6.Certificate.GramAssembly.Block1

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_20_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_20_e_oai
