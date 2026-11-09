-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:45:24.513037+00:00
-- url     : https://prove2.me/submissions/81a8aac8-615a-4a3c-9801-00b7b8d3661b

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Part4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem node130_check : node130 =
    Integer.Sparse.merge (Integer.Sparse.scale (1215062) entry_5_1) (Integer.Sparse.scale (2092458) entry_5_2) := by decide +kernel

theorem node130_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node130 x = (((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x) := by
  rw [node130_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node131_check : node131 =
    Integer.Sparse.merge (Integer.Sparse.scale (-348911) entry_5_0) node130 := by decide +kernel

theorem node131_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node131 x = (((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) := by
  rw [node131_check, Integer.Sparse.eval_merge]
  rw [node130_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node132_check : node132 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1491868) entry_5_4) (Integer.Sparse.scale (6691737) entry_5_5) := by decide +kernel

theorem node132_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node132 x = (((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((6691737 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x) := by
  rw [node132_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node133_check : node133 =
    Integer.Sparse.merge (Integer.Sparse.scale (-427246) entry_5_3) node132 := by decide +kernel

theorem node133_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node133 x = (((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((6691737 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x)) := by
  rw [node133_check, Integer.Sparse.eval_merge]
  rw [node132_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node134_check : node134 =
    Integer.Sparse.merge node131 node133 := by decide +kernel

theorem node134_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node134 x = ((((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) + (((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((6691737 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x))) := by
  rw [node134_check, Integer.Sparse.eval_merge]
  rw [node131_eval, node133_eval]

theorem node135_check : node135 =
    Integer.Sparse.merge (Integer.Sparse.scale (2447831) entry_5_7) (Integer.Sparse.scale (-2470731) entry_5_8) := by decide +kernel

theorem node135_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node135 x = (((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x) := by
  rw [node135_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node136_check : node136 =
    Integer.Sparse.merge (Integer.Sparse.scale (-614723) entry_5_6) node135 := by decide +kernel

theorem node136_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node136 x = (((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) := by
  rw [node136_check, Integer.Sparse.eval_merge]
  rw [node135_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node137_check : node137 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3927318) entry_5_9) (Integer.Sparse.scale (469732) entry_5_10) := by decide +kernel

theorem node137_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node137 x = (((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) := by
  rw [node137_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node138_check : node138 =
    Integer.Sparse.merge (Integer.Sparse.scale (-959011) entry_5_11) (Integer.Sparse.scale (-1289212) entry_5_12) := by decide +kernel

theorem node138_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node138 x = (((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x) := by
  rw [node138_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node139_check : node139 =
    Integer.Sparse.merge node137 node138 := by decide +kernel

theorem node139_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node139 x = ((((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) + (((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x)) := by
  rw [node139_check, Integer.Sparse.eval_merge]
  rw [node137_eval, node138_eval]

theorem node140_check : node140 =
    Integer.Sparse.merge node136 node139 := by decide +kernel

theorem node140_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node140 x = ((((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + ((((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) + (((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x))) := by
  rw [node140_check, Integer.Sparse.eval_merge]
  rw [node136_eval, node139_eval]

theorem node141_check : node141 =
    Integer.Sparse.merge node134 node140 := by decide +kernel

theorem node141_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node141 x = (((((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) + (((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((6691737 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x))) + ((((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + ((((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) + (((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x)))) := by
  rw [node141_check, Integer.Sparse.eval_merge]
  rw [node134_eval, node140_eval]

theorem node142_check : node142 =
    Integer.Sparse.merge (Integer.Sparse.scale (995398) entry_5_14) (Integer.Sparse.scale (-3671401) entry_5_15) := by decide +kernel

theorem node142_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node142 x = (((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x) := by
  rw [node142_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node143_check : node143 =
    Integer.Sparse.merge (Integer.Sparse.scale (420869) entry_5_13) node142 := by decide +kernel

theorem node143_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node143 x = (((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x)) := by
  rw [node143_check, Integer.Sparse.eval_merge]
  rw [node142_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node144_check : node144 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3970214) entry_5_16) (Integer.Sparse.scale (728173) entry_5_17) := by decide +kernel

theorem node144_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node144 x = (((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x) := by
  rw [node144_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node145_check : node145 =
    Integer.Sparse.merge (Integer.Sparse.scale (1583616) entry_5_18) (Integer.Sparse.scale (-2751073) entry_5_19) := by decide +kernel

theorem node145_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node145 x = (((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x) := by
  rw [node145_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node146_check : node146 =
    Integer.Sparse.merge node144 node145 := by decide +kernel

theorem node146_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node146 x = ((((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x) + (((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x)) := by
  rw [node146_check, Integer.Sparse.eval_merge]
  rw [node144_eval, node145_eval]

theorem node147_check : node147 =
    Integer.Sparse.merge node143 node146 := by decide +kernel

theorem node147_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node147 x = ((((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x)) + ((((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x) + (((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x))) := by
  rw [node147_check, Integer.Sparse.eval_merge]
  rw [node143_eval, node146_eval]

theorem node148_check : node148 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2391480) entry_5_21) (Integer.Sparse.scale (1842073) entry_5_22) := by decide +kernel

theorem node148_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node148 x = (((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_22 x) := by
  rw [node148_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node149_check : node149 =
    Integer.Sparse.merge (Integer.Sparse.scale (-341589) entry_5_20) node148 := by decide +kernel

theorem node149_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node149 x = (((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + (((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_22 x)) := by
  rw [node149_check, Integer.Sparse.eval_merge]
  rw [node148_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node150_check : node150 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3406562) entry_5_23) (Integer.Sparse.scale (619147) entry_5_24) := by decide +kernel

theorem node150_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node150 x = (((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_23 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_24 x) := by
  rw [node150_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node151_check : node151 =
    Integer.Sparse.merge (Integer.Sparse.scale (869639) entry_5_25) (Integer.Sparse.scale (-393268) entry_5_26) := by decide +kernel

theorem node151_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node151 x = (((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_25 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_26 x) := by
  rw [node151_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

theorem node152_check : node152 =
    Integer.Sparse.merge node150 node151 := by decide +kernel

theorem node152_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node152 x = ((((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_23 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_24 x) + (((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_25 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_26 x)) := by
  rw [node152_check, Integer.Sparse.eval_merge]
  rw [node150_eval, node151_eval]

theorem node153_check : node153 =
    Integer.Sparse.merge node149 node152 := by decide +kernel

theorem node153_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node153 x = ((((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + (((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_22 x)) + ((((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_23 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_24 x) + (((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_25 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_26 x))) := by
  rw [node153_check, Integer.Sparse.eval_merge]
  rw [node149_eval, node152_eval]

theorem node154_check : node154 =
    Integer.Sparse.merge node147 node153 := by decide +kernel

theorem node154_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node154 x = (((((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x)) + ((((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x) + (((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x))) + ((((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + (((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_22 x)) + ((((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_23 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_24 x) + (((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_25 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_26 x)))) := by
  rw [node154_check, Integer.Sparse.eval_merge]
  rw [node147_eval, node153_eval]

theorem node155_check : node155 =
    Integer.Sparse.merge node141 node154 := by decide +kernel

theorem node155_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node155 x = ((((((-348911 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_0 x + (((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_1 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_2 x)) + (((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_3 x + (((-1491868 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_4 x + ((6691737 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_5 x))) + ((((-614723 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_6 x + (((2447831 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_7 x + ((-2470731 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_8 x)) + ((((-3927318 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_9 x + ((469732 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_10 x) + (((-959011 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_11 x + ((-1289212 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_12 x)))) + (((((420869 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_13 x + (((995398 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_14 x + ((-3671401 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_15 x)) + ((((-3970214 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_16 x + ((728173 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_17 x) + (((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_18 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_19 x))) + ((((-341589 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_20 x + (((-2391480 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_21 x + ((1842073 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_22 x)) + ((((-3406562 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_23 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_24 x) + (((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_25 x + ((-393268 : ℤ) : ℝ) * Integer.Sparse.eval entry_5_26 x))))) := by
  rw [node155_check, Integer.Sparse.eval_merge]
  rw [node141_eval, node154_eval]

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

theorem row_eval_5_e_oai (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node155 x =
      ∑ j : Fin 27, (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x := by
  rw [node155_eval]
  exact (sum_expand_27 (fun j => (weights 5 j : ℝ) * Integer.Sparse.eval (entries 5 j) x)).symm

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.row_eval_5_e_oai
