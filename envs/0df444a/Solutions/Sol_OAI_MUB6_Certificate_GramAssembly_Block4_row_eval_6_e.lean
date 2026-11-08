-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:49:02.375744+00:00
-- url     : https://prove2.me/submissions/f5191a5b-0c9c-4023-845b-82ee7de5cf13

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E007
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node126_check : node126 =
    Integer.Sparse.merge (Integer.Sparse.scale (2181374) entry_6_0) (Integer.Sparse.scale (6647397) entry_6_1) := by decide +kernel

theorem node126_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node126 x = (((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) := by
  rw [node126_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node127_check : node127 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4628999) entry_6_3) (Integer.Sparse.scale (3463174) entry_6_4) := by decide +kernel

theorem node127_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node127 x = (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x) := by
  rw [node127_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node128_check : node128 =
    Integer.Sparse.merge (Integer.Sparse.scale (8255371) entry_6_2) node127 := by decide +kernel

theorem node128_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node128 x = (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x)) := by
  rw [node128_check, Integer.Sparse.eval_merge]
  rw [node127_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node129_check : node129 =
    Integer.Sparse.merge node126 node128 := by decide +kernel

theorem node129_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node129 x = ((((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) := by
  rw [node129_check, Integer.Sparse.eval_merge]
  rw [node126_eval, node128_eval]

theorem node130_check : node130 =
    Integer.Sparse.merge (Integer.Sparse.scale (48094530) entry_6_6) (Integer.Sparse.scale (-7277099) entry_6_7) := by decide +kernel

theorem node130_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node130 x = (((48094530 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x) := by
  rw [node130_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node131_check : node131 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4702242) entry_6_5) node130 := by decide +kernel

theorem node131_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node131 x = (((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((48094530 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) := by
  rw [node131_check, Integer.Sparse.eval_merge]
  rw [node130_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node132_check : node132 =
    Integer.Sparse.merge (Integer.Sparse.scale (-158959) entry_6_9) (Integer.Sparse.scale (32218355) entry_6_10) := by decide +kernel

theorem node132_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node132 x = (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x) := by
  rw [node132_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node133_check : node133 =
    Integer.Sparse.merge (Integer.Sparse.scale (8611573) entry_6_8) node132 := by decide +kernel

theorem node133_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node133 x = (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x)) := by
  rw [node133_check, Integer.Sparse.eval_merge]
  rw [node132_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node134_check : node134 =
    Integer.Sparse.merge node131 node133 := by decide +kernel

theorem node134_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node134 x = ((((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((48094530 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x))) := by
  rw [node134_check, Integer.Sparse.eval_merge]
  rw [node131_eval, node133_eval]

theorem node135_check : node135 =
    Integer.Sparse.merge node129 node134 := by decide +kernel

theorem node135_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node135 x = (((((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) + ((((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((48094530 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x)))) := by
  rw [node135_check, Integer.Sparse.eval_merge]
  rw [node129_eval, node134_eval]

theorem node136_check : node136 =
    Integer.Sparse.merge (Integer.Sparse.scale (4328739) entry_6_11) (Integer.Sparse.scale (-12463162) entry_6_12) := by decide +kernel

theorem node136_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node136 x = (((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x) := by
  rw [node136_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node137_check : node137 =
    Integer.Sparse.merge (Integer.Sparse.scale (42159577) entry_6_14) (Integer.Sparse.scale (30525040) entry_6_15) := by decide +kernel

theorem node137_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node137 x = (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x) := by
  rw [node137_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node138_check : node138 =
    Integer.Sparse.merge (Integer.Sparse.scale (-826686) entry_6_13) node137 := by decide +kernel

theorem node138_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node138 x = (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x)) := by
  rw [node138_check, Integer.Sparse.eval_merge]
  rw [node137_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node139_check : node139 =
    Integer.Sparse.merge node136 node138 := by decide +kernel

theorem node139_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node139 x = ((((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x) + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x))) := by
  rw [node139_check, Integer.Sparse.eval_merge]
  rw [node136_eval, node138_eval]

theorem node140_check : node140 =
    Integer.Sparse.merge (Integer.Sparse.scale (5748703) entry_6_17) (Integer.Sparse.scale (677023) entry_6_18) := by decide +kernel

theorem node140_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node140 x = (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x + ((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x) := by
  rw [node140_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node141_check : node141 =
    Integer.Sparse.merge (Integer.Sparse.scale (-26700880) entry_6_16) node140 := by decide +kernel

theorem node141_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node141 x = (((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x + ((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x)) := by
  rw [node141_check, Integer.Sparse.eval_merge]
  rw [node140_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node142_check : node142 =
    Integer.Sparse.merge (Integer.Sparse.scale (9575677) entry_6_20) (Integer.Sparse.scale (17455872) entry_6_21) := by decide +kernel

theorem node142_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node142 x = (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + ((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x) := by
  rw [node142_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node143_check : node143 =
    Integer.Sparse.merge (Integer.Sparse.scale (-524585) entry_6_19) node142 := by decide +kernel

theorem node143_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node143 x = (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + ((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x)) := by
  rw [node143_check, Integer.Sparse.eval_merge]
  rw [node142_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node144_check : node144 =
    Integer.Sparse.merge node141 node143 := by decide +kernel

theorem node144_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node144 x = ((((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x + ((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x)) + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + ((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x))) := by
  rw [node144_check, Integer.Sparse.eval_merge]
  rw [node141_eval, node143_eval]

theorem node145_check : node145 =
    Integer.Sparse.merge node139 node144 := by decide +kernel

theorem node145_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node145 x = (((((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x) + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x))) + ((((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x + ((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x)) + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + ((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x)))) := by
  rw [node145_check, Integer.Sparse.eval_merge]
  rw [node139_eval, node144_eval]

theorem node146_check : node146 =
    Integer.Sparse.merge node135 node145 := by decide +kernel

theorem node146_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node146 x = ((((((2181374 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_0 x + ((6647397 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_1 x) + (((8255371 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_2 x + (((-4628999 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_3 x + ((3463174 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_4 x))) + ((((-4702242 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_5 x + (((48094530 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_6 x + ((-7277099 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_7 x)) + (((8611573 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_8 x + (((-158959 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_9 x + ((32218355 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_10 x)))) + (((((4328739 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_11 x + ((-12463162 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_12 x) + (((-826686 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_13 x + (((42159577 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_14 x + ((30525040 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_15 x))) + ((((-26700880 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_16 x + (((5748703 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_17 x + ((677023 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_18 x)) + (((-524585 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_19 x + (((9575677 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_20 x + ((17455872 : ℤ) : ℝ) * Integer.Sparse.eval entry_6_21 x))))) := by
  rw [node146_check, Integer.Sparse.eval_merge]
  rw [node135_eval, node145_eval]

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

theorem row_eval_6_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node146 x =
      ∑ j : Fin 22, (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x := by
  rw [node146_eval]
  exact (sum_expand_22 (fun j => (weights 6 j : ℝ) * Integer.Sparse.eval (entries 6 j) x)).symm

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_6_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_6_e_oai
