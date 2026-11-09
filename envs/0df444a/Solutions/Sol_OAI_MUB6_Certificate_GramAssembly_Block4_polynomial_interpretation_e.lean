-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:25:46.945207+00:00
-- url     : https://prove2.me/submissions/cd22f233-c2ec-4a0b-970a-3d96fa2ee7bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E012
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E151
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_indexed_entry_eval_e
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_rows_eval_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

theorem weights_cast_0 (j : Fin 22) :
    (weights 0 j : ℚ) = GramData.Block4.Z 0 j := by
  revert j
  decide +kernel

theorem weights_cast_1 (j : Fin 22) :
    (weights 1 j : ℚ) = GramData.Block4.Z 1 j := by
  revert j
  decide +kernel

theorem weights_cast_2 (j : Fin 22) :
    (weights 2 j : ℚ) = GramData.Block4.Z 2 j := by
  revert j
  decide +kernel

theorem weights_cast_3 (j : Fin 22) :
    (weights 3 j : ℚ) = GramData.Block4.Z 3 j := by
  revert j
  decide +kernel

theorem weights_cast_4 (j : Fin 22) :
    (weights 4 j : ℚ) = GramData.Block4.Z 4 j := by
  revert j
  decide +kernel

theorem weights_cast_5 (j : Fin 22) :
    (weights 5 j : ℚ) = GramData.Block4.Z 5 j := by
  revert j
  decide +kernel

theorem weights_cast_6 (j : Fin 22) :
    (weights 6 j : ℚ) = GramData.Block4.Z 6 j := by
  revert j
  decide +kernel

theorem weights_cast_7 (j : Fin 22) :
    (weights 7 j : ℚ) = GramData.Block4.Z 7 j := by
  revert j
  decide +kernel

theorem weights_cast_8 (j : Fin 22) :
    (weights 8 j : ℚ) = GramData.Block4.Z 8 j := by
  revert j
  decide +kernel

theorem weights_cast_9 (j : Fin 22) :
    (weights 9 j : ℚ) = GramData.Block4.Z 9 j := by
  revert j
  decide +kernel

theorem weights_cast_10 (j : Fin 22) :
    (weights 10 j : ℚ) = GramData.Block4.Z 10 j := by
  revert j
  decide +kernel

theorem weights_cast_11 (j : Fin 22) :
    (weights 11 j : ℚ) = GramData.Block4.Z 11 j := by
  revert j
  decide +kernel

theorem weights_cast_12 (j : Fin 22) :
    (weights 12 j : ℚ) = GramData.Block4.Z 12 j := by
  revert j
  decide +kernel

theorem weights_cast_13 (j : Fin 22) :
    (weights 13 j : ℚ) = GramData.Block4.Z 13 j := by
  revert j
  decide +kernel

theorem weights_cast_14 (j : Fin 22) :
    (weights 14 j : ℚ) = GramData.Block4.Z 14 j := by
  revert j
  decide +kernel

theorem weights_cast_15 (j : Fin 22) :
    (weights 15 j : ℚ) = GramData.Block4.Z 15 j := by
  revert j
  decide +kernel

theorem weights_cast_16 (j : Fin 22) :
    (weights 16 j : ℚ) = GramData.Block4.Z 16 j := by
  revert j
  decide +kernel

theorem weights_cast_17 (j : Fin 22) :
    (weights 17 j : ℚ) = GramData.Block4.Z 17 j := by
  revert j
  decide +kernel

theorem weights_cast_18 (j : Fin 22) :
    (weights 18 j : ℚ) = GramData.Block4.Z 18 j := by
  revert j
  decide +kernel

theorem weights_cast_19 (j : Fin 22) :
    (weights 19 j : ℚ) = GramData.Block4.Z 19 j := by
  revert j
  decide +kernel

theorem weights_cast_20 (j : Fin 22) :
    (weights 20 j : ℚ) = GramData.Block4.Z 20 j := by
  revert j
  decide +kernel

theorem weights_cast_21 (j : Fin 22) :
    (weights 21 j : ℚ) = GramData.Block4.Z 21 j := by
  revert j
  decide +kernel

theorem weights_cast (i j : Fin 22) :
    (weights i j : ℚ) = GramData.Block4.Z i j := by
  fin_cases i
  · exact weights_cast_0 j
  · exact weights_cast_1 j
  · exact weights_cast_2 j
  · exact weights_cast_3 j
  · exact weights_cast_4 j
  · exact weights_cast_5 j
  · exact weights_cast_6 j
  · exact weights_cast_7 j
  · exact weights_cast_8 j
  · exact weights_cast_9 j
  · exact weights_cast_10 j
  · exact weights_cast_11 j
  · exact weights_cast_12 j
  · exact weights_cast_13 j
  · exact weights_cast_14 j
  · exact weights_cast_15 j
  · exact weights_cast_16 j
  · exact weights_cast_17 j
  · exact weights_cast_18 j
  · exact weights_cast_19 j
  · exact weights_cast_20 j
  · exact weights_cast_21 j

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

theorem node462_check : node462 =
    Integer.Sparse.merge node20 node41 := by decide +kernel

theorem node462_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node462 x = (Integer.Sparse.eval node20 x + Integer.Sparse.eval node41 x) := by
  rw [node462_check, Integer.Sparse.eval_merge]

theorem node463_check : node463 =
    Integer.Sparse.merge node83 node104 := by decide +kernel

theorem node463_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node463 x = (Integer.Sparse.eval node83 x + Integer.Sparse.eval node104 x) := by
  rw [node463_check, Integer.Sparse.eval_merge]

theorem node464_check : node464 =
    Integer.Sparse.merge node62 node463 := by decide +kernel

theorem node464_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node464 x = (Integer.Sparse.eval node62 x + (Integer.Sparse.eval node83 x + Integer.Sparse.eval node104 x)) := by
  rw [node464_check, Integer.Sparse.eval_merge]
  rw [node463_eval]

theorem node465_check : node465 =
    Integer.Sparse.merge node462 node464 := by decide +kernel

theorem node465_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node465 x = ((Integer.Sparse.eval node20 x + Integer.Sparse.eval node41 x) + (Integer.Sparse.eval node62 x + (Integer.Sparse.eval node83 x + Integer.Sparse.eval node104 x))) := by
  rw [node465_check, Integer.Sparse.eval_merge]
  rw [node462_eval, node464_eval]

theorem node466_check : node466 =
    Integer.Sparse.merge node146 node167 := by decide +kernel

theorem node466_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node466 x = (Integer.Sparse.eval node146 x + Integer.Sparse.eval node167 x) := by
  rw [node466_check, Integer.Sparse.eval_merge]

theorem node467_check : node467 =
    Integer.Sparse.merge node125 node466 := by decide +kernel

theorem node467_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node467 x = (Integer.Sparse.eval node125 x + (Integer.Sparse.eval node146 x + Integer.Sparse.eval node167 x)) := by
  rw [node467_check, Integer.Sparse.eval_merge]
  rw [node466_eval]

theorem node468_check : node468 =
    Integer.Sparse.merge node209 node230 := by decide +kernel

theorem node468_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node468 x = (Integer.Sparse.eval node209 x + Integer.Sparse.eval node230 x) := by
  rw [node468_check, Integer.Sparse.eval_merge]

theorem node469_check : node469 =
    Integer.Sparse.merge node188 node468 := by decide +kernel

theorem node469_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node469 x = (Integer.Sparse.eval node188 x + (Integer.Sparse.eval node209 x + Integer.Sparse.eval node230 x)) := by
  rw [node469_check, Integer.Sparse.eval_merge]
  rw [node468_eval]

theorem node470_check : node470 =
    Integer.Sparse.merge node467 node469 := by decide +kernel

theorem node470_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node470 x = ((Integer.Sparse.eval node125 x + (Integer.Sparse.eval node146 x + Integer.Sparse.eval node167 x)) + (Integer.Sparse.eval node188 x + (Integer.Sparse.eval node209 x + Integer.Sparse.eval node230 x))) := by
  rw [node470_check, Integer.Sparse.eval_merge]
  rw [node467_eval, node469_eval]

theorem node471_check : node471 =
    Integer.Sparse.merge node465 node470 := by decide +kernel

theorem node471_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node471 x = (((Integer.Sparse.eval node20 x + Integer.Sparse.eval node41 x) + (Integer.Sparse.eval node62 x + (Integer.Sparse.eval node83 x + Integer.Sparse.eval node104 x))) + ((Integer.Sparse.eval node125 x + (Integer.Sparse.eval node146 x + Integer.Sparse.eval node167 x)) + (Integer.Sparse.eval node188 x + (Integer.Sparse.eval node209 x + Integer.Sparse.eval node230 x)))) := by
  rw [node471_check, Integer.Sparse.eval_merge]
  rw [node465_eval, node470_eval]

theorem node472_check : node472 =
    Integer.Sparse.merge node251 node272 := by decide +kernel

theorem node472_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node472 x = (Integer.Sparse.eval node251 x + Integer.Sparse.eval node272 x) := by
  rw [node472_check, Integer.Sparse.eval_merge]

theorem node473_check : node473 =
    Integer.Sparse.merge node314 node335 := by decide +kernel

theorem node473_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node473 x = (Integer.Sparse.eval node314 x + Integer.Sparse.eval node335 x) := by
  rw [node473_check, Integer.Sparse.eval_merge]

theorem node474_check : node474 =
    Integer.Sparse.merge node293 node473 := by decide +kernel

theorem node474_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node474 x = (Integer.Sparse.eval node293 x + (Integer.Sparse.eval node314 x + Integer.Sparse.eval node335 x)) := by
  rw [node474_check, Integer.Sparse.eval_merge]
  rw [node473_eval]

theorem node475_check : node475 =
    Integer.Sparse.merge node472 node474 := by decide +kernel

theorem node475_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node475 x = ((Integer.Sparse.eval node251 x + Integer.Sparse.eval node272 x) + (Integer.Sparse.eval node293 x + (Integer.Sparse.eval node314 x + Integer.Sparse.eval node335 x))) := by
  rw [node475_check, Integer.Sparse.eval_merge]
  rw [node472_eval, node474_eval]

theorem node476_check : node476 =
    Integer.Sparse.merge node377 node398 := by decide +kernel

theorem node476_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node476 x = (Integer.Sparse.eval node377 x + Integer.Sparse.eval node398 x) := by
  rw [node476_check, Integer.Sparse.eval_merge]

theorem node477_check : node477 =
    Integer.Sparse.merge node356 node476 := by decide +kernel

theorem node477_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node477 x = (Integer.Sparse.eval node356 x + (Integer.Sparse.eval node377 x + Integer.Sparse.eval node398 x)) := by
  rw [node477_check, Integer.Sparse.eval_merge]
  rw [node476_eval]

theorem node478_check : node478 =
    Integer.Sparse.merge node440 node461 := by decide +kernel

theorem node478_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node478 x = (Integer.Sparse.eval node440 x + Integer.Sparse.eval node461 x) := by
  rw [node478_check, Integer.Sparse.eval_merge]

theorem node479_check : node479 =
    Integer.Sparse.merge node419 node478 := by decide +kernel

theorem node479_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node479 x = (Integer.Sparse.eval node419 x + (Integer.Sparse.eval node440 x + Integer.Sparse.eval node461 x)) := by
  rw [node479_check, Integer.Sparse.eval_merge]
  rw [node478_eval]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Part15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem node480_check : node480 =
    Integer.Sparse.merge node477 node479 := by decide +kernel

theorem node480_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node480 x = ((Integer.Sparse.eval node356 x + (Integer.Sparse.eval node377 x + Integer.Sparse.eval node398 x)) + (Integer.Sparse.eval node419 x + (Integer.Sparse.eval node440 x + Integer.Sparse.eval node461 x))) := by
  rw [node480_check, Integer.Sparse.eval_merge]
  rw [node477_eval, node479_eval]

theorem node481_check : node481 =
    Integer.Sparse.merge node475 node480 := by decide +kernel

theorem node481_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node481 x = (((Integer.Sparse.eval node251 x + Integer.Sparse.eval node272 x) + (Integer.Sparse.eval node293 x + (Integer.Sparse.eval node314 x + Integer.Sparse.eval node335 x))) + ((Integer.Sparse.eval node356 x + (Integer.Sparse.eval node377 x + Integer.Sparse.eval node398 x)) + (Integer.Sparse.eval node419 x + (Integer.Sparse.eval node440 x + Integer.Sparse.eval node461 x)))) := by
  rw [node481_check, Integer.Sparse.eval_merge]
  rw [node475_eval, node480_eval]

theorem node482_check : node482 =
    Integer.Sparse.merge node471 node481 := by decide +kernel

theorem node482_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node482 x = ((((Integer.Sparse.eval node20 x + Integer.Sparse.eval node41 x) + (Integer.Sparse.eval node62 x + (Integer.Sparse.eval node83 x + Integer.Sparse.eval node104 x))) + ((Integer.Sparse.eval node125 x + (Integer.Sparse.eval node146 x + Integer.Sparse.eval node167 x)) + (Integer.Sparse.eval node188 x + (Integer.Sparse.eval node209 x + Integer.Sparse.eval node230 x)))) + (((Integer.Sparse.eval node251 x + Integer.Sparse.eval node272 x) + (Integer.Sparse.eval node293 x + (Integer.Sparse.eval node314 x + Integer.Sparse.eval node335 x))) + ((Integer.Sparse.eval node356 x + (Integer.Sparse.eval node377 x + Integer.Sparse.eval node398 x)) + (Integer.Sparse.eval node419 x + (Integer.Sparse.eval node440 x + Integer.Sparse.eval node461 x))))) := by
  rw [node482_check, Integer.Sparse.eval_merge]
  rw [node471_eval, node481_eval]

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

theorem polynomial_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval polynomial x =
      ∑ i : Fin 22, ∑ j : Fin 22, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  calc
    _ = ∑ i : Fin 22, Integer.Sparse.eval (rows i) x := by
      rw [polynomial, node482_eval]
      exact (sum_expand_22 (fun i => Integer.Sparse.eval (rows i) x)).symm
    _ = _ := by simp_rw [rows_eval_e]

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block4

theorem weights_real (i j : Fin 22) :
    (weights i j : ℝ) = realMatrix GramData.Block4.Z i j := by
  change (weights i j : ℝ) = (GramData.Block4.Z i j : ℝ)
  exact_mod_cast weights_cast i j

theorem polynomial_interpretation_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.quadratic4 B := by
  rw [polynomial_eval]
  unfold GramNonnegative.quadratic4
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [indexed_entry_eval_e i j B hB, weights_real]

end MUB6.Certificate.GramAssembly.Block4

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.polynomial_interpretation_e_oai
