-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:48:57.8021+00:00
-- url     : https://prove2.me/submissions/0fb0aa48-016a-4056-9425-a36bb0b8979b

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node441_check : node441 =
    Integer.Sparse.merge (Integer.Sparse.scale (-15099711) entry_21_0) (Integer.Sparse.scale (6258575) entry_21_1) := by decide +kernel

theorem node441_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node441 x = (((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x) := by
  rw [node441_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node442_check : node442 =
    Integer.Sparse.merge (Integer.Sparse.scale (7350062) entry_21_3) (Integer.Sparse.scale (3505349) entry_21_4) := by decide +kernel

theorem node442_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node442 x = (((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x) := by
  rw [node442_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node443_check : node443 =
    Integer.Sparse.merge (Integer.Sparse.scale (220430) entry_21_2) node442 := by decide +kernel

theorem node443_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node443 x = (((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x + (((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x)) := by
  rw [node443_check, Integer.Sparse.eval_merge]
  rw [node442_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node444_check : node444 =
    Integer.Sparse.merge node441 node443 := by decide +kernel

theorem node444_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node444 x = ((((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x) + (((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x + (((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x))) := by
  rw [node444_check, Integer.Sparse.eval_merge]
  rw [node441_eval, node443_eval]

theorem node445_check : node445 =
    Integer.Sparse.merge (Integer.Sparse.scale (17455872) entry_21_6) (Integer.Sparse.scale (-8777026) entry_21_7) := by decide +kernel

theorem node445_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node445 x = (((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x) := by
  rw [node445_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node446_check : node446 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3345646) entry_21_5) node445 := by decide +kernel

theorem node446_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node446 x = (((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x + (((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x)) := by
  rw [node446_check, Integer.Sparse.eval_merge]
  rw [node445_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node447_check : node447 =
    Integer.Sparse.merge (Integer.Sparse.scale (-11111890) entry_21_9) (Integer.Sparse.scale (2653116) entry_21_10) := by decide +kernel

theorem node447_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node447 x = (((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x) := by
  rw [node447_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node448_check : node448 =
    Integer.Sparse.merge (Integer.Sparse.scale (2493568) entry_21_8) node447 := by decide +kernel

theorem node448_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node448 x = (((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x + (((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x)) := by
  rw [node448_check, Integer.Sparse.eval_merge]
  rw [node447_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node449_check : node449 =
    Integer.Sparse.merge node446 node448 := by decide +kernel

theorem node449_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node449 x = ((((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x + (((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x)) + (((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x + (((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x))) := by
  rw [node449_check, Integer.Sparse.eval_merge]
  rw [node446_eval, node448_eval]

theorem node450_check : node450 =
    Integer.Sparse.merge node444 node449 := by decide +kernel

theorem node450_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node450 x = (((((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x) + (((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x + (((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x))) + ((((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x + (((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x)) + (((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x + (((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x)))) := by
  rw [node450_check, Integer.Sparse.eval_merge]
  rw [node444_eval, node449_eval]

theorem node451_check : node451 =
    Integer.Sparse.merge (Integer.Sparse.scale (787079) entry_21_11) (Integer.Sparse.scale (-3952727) entry_21_12) := by decide +kernel

theorem node451_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node451 x = (((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x) := by
  rw [node451_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node452_check : node452 =
    Integer.Sparse.merge (Integer.Sparse.scale (11611437) entry_21_14) (Integer.Sparse.scale (25550802) entry_21_15) := by decide +kernel

theorem node452_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node452 x = (((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x) := by
  rw [node452_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node453_check : node453 =
    Integer.Sparse.merge (Integer.Sparse.scale (7485003) entry_21_13) node452 := by decide +kernel

theorem node453_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node453 x = (((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x)) := by
  rw [node453_check, Integer.Sparse.eval_merge]
  rw [node452_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node454_check : node454 =
    Integer.Sparse.merge node451 node453 := by decide +kernel

theorem node454_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node454 x = ((((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x) + (((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x))) := by
  rw [node454_check, Integer.Sparse.eval_merge]
  rw [node451_eval, node453_eval]

theorem node455_check : node455 =
    Integer.Sparse.merge (Integer.Sparse.scale (5047208) entry_21_17) (Integer.Sparse.scale (6360316) entry_21_18) := by decide +kernel

theorem node455_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node455 x = (((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x) := by
  rw [node455_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node456_check : node456 =
    Integer.Sparse.merge (Integer.Sparse.scale (-47014529) entry_21_16) node455 := by decide +kernel

theorem node456_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node456 x = (((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + (((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x)) := by
  rw [node456_check, Integer.Sparse.eval_merge]
  rw [node455_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node457_check : node457 =
    Integer.Sparse.merge (Integer.Sparse.scale (20619430) entry_21_20) (Integer.Sparse.scale (50740836) entry_21_21) := by decide +kernel

theorem node457_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node457 x = (((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + ((50740836 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x) := by
  rw [node457_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node458_check : node458 =
    Integer.Sparse.merge (Integer.Sparse.scale (847534) entry_21_19) node457 := by decide +kernel

theorem node458_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node458 x = (((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x + (((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + ((50740836 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x)) := by
  rw [node458_check, Integer.Sparse.eval_merge]
  rw [node457_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node459_check : node459 =
    Integer.Sparse.merge node456 node458 := by decide +kernel

theorem node459_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node459 x = ((((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + (((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x)) + (((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x + (((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + ((50740836 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x))) := by
  rw [node459_check, Integer.Sparse.eval_merge]
  rw [node456_eval, node458_eval]

theorem node460_check : node460 =
    Integer.Sparse.merge node454 node459 := by decide +kernel

theorem node460_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node460 x = (((((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x) + (((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x))) + ((((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + (((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x)) + (((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x + (((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + ((50740836 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x)))) := by
  rw [node460_check, Integer.Sparse.eval_merge]
  rw [node454_eval, node459_eval]

theorem node461_check : node461 =
    Integer.Sparse.merge node450 node460 := by decide +kernel

theorem node461_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node461 x = ((((((-15099711 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_0 x + ((6258575 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_1 x) + (((220430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_2 x + (((7350062 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_3 x + ((3505349 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_4 x))) + ((((-3345646 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_5 x + (((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_6 x + ((-8777026 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_7 x)) + (((2493568 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_8 x + (((-11111890 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_9 x + ((2653116 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_10 x)))) + (((((787079 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_11 x + ((-3952727 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_12 x) + (((7485003 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_13 x + (((11611437 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_14 x + ((25550802 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_15 x))) + ((((-47014529 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_16 x + (((5047208 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_17 x + ((6360316 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_18 x)) + (((847534 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_19 x + (((20619430 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_20 x + ((50740836 : ℤ) : ℝ) * Integer.Sparse.eval entry_21_21 x))))) := by
  rw [node461_check, Integer.Sparse.eval_merge]
  rw [node450_eval, node460_eval]

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

theorem row_eval_21_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node461 x =
      ∑ j : Fin 22, (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x := by
  rw [node461_eval]
  exact (sum_expand_22 (fun j => (weights 21 j : ℝ) * Integer.Sparse.eval (entries 21 j) x)).symm

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_21_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_21_e_oai
