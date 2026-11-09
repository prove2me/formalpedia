-- Prove2me | solution 1 for OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:25:23.550681+00:00
-- url     : https://prove2.me/submissions/35fcf945-747c-49a5-9fcb-7d9d33e0877b

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E149
import Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_allRowsSound_e

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

theorem eval_perm {a b : Sparse ι} (h : a.Perm b) (x : ι → ℝ) :
    eval a x = eval b x := by
  unfold eval
  exact (h.map fun p : ι × ℤ => (p.2 : ℝ) * x p.1).sum_eq

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck0 : pairMerged0 = Integer.Sparse.merge (Integer.Sparse.scale (-499592880) (rows 1)) (Integer.Sparse.scale (361260120) (rows 2)) := by decide +kernel

theorem pairMergedZero0 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged0 x = 0 := by
  rw [pairMergeCheck0, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck1 : pairMerged1 = Integer.Sparse.merge (Integer.Sparse.scale (-74130400) (rows 0)) pairMerged0 := by decide +kernel

theorem pairMergedZero1 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged1 x = 0 := by
  rw [pairMergeCheck1, Integer.Sparse.eval_merge]
  rw [pairMergedZero0 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck2 : pairMerged2 = Integer.Sparse.merge (Integer.Sparse.scale (41297184) (rows 3)) (Integer.Sparse.scale (-93347246) (rows 4)) := by decide +kernel

theorem pairMergedZero2 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged2 x = 0 := by
  rw [pairMergeCheck2, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck3 : pairMerged3 = Integer.Sparse.merge (Integer.Sparse.scale (45411996) (rows 5)) (Integer.Sparse.scale (67604976) (rows 6)) := by decide +kernel

theorem pairMergedZero3 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged3 x = 0 := by
  rw [pairMergeCheck3, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck4 : pairMerged4 = Integer.Sparse.merge pairMerged2 pairMerged3 := by decide +kernel

theorem pairMergedZero4 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged4 x = 0 := by
  rw [pairMergeCheck4, Integer.Sparse.eval_merge]
  rw [pairMergedZero2 x h, pairMergedZero3 x h]
  simp only [add_zero]

theorem pairMergeCheck5 : pairMerged5 = Integer.Sparse.merge pairMerged1 pairMerged4 := by decide +kernel

theorem pairMergedZero5 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged5 x = 0 := by
  rw [pairMergeCheck5, Integer.Sparse.eval_merge]
  rw [pairMergedZero1 x h, pairMergedZero4 x h]
  simp only [add_zero]

theorem pairMergeCheck6 : pairMerged6 = Integer.Sparse.merge (Integer.Sparse.scale (-59688240) (rows 7)) (Integer.Sparse.scale (-2886108) (rows 8)) := by decide +kernel

theorem pairMergedZero6 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged6 x = 0 := by
  rw [pairMergeCheck6, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck7 : pairMerged7 = Integer.Sparse.merge (Integer.Sparse.scale (3758532) (rows 9)) (Integer.Sparse.scale (-4396968) (rows 10)) := by decide +kernel

theorem pairMergedZero7 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged7 x = 0 := by
  rw [pairMergeCheck7, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck8 : pairMerged8 = Integer.Sparse.merge pairMerged6 pairMerged7 := by decide +kernel

theorem pairMergedZero8 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged8 x = 0 := by
  rw [pairMergeCheck8, Integer.Sparse.eval_merge]
  rw [pairMergedZero6 x h, pairMergedZero7 x h]
  simp only [add_zero]

theorem pairMergeCheck9 : pairMerged9 = Integer.Sparse.merge (Integer.Sparse.scale (-2284320) (rows 11)) (Integer.Sparse.scale (43313040) (rows 12)) := by decide +kernel

theorem pairMergedZero9 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged9 x = 0 := by
  rw [pairMergeCheck9, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck10 : pairMerged10 = Integer.Sparse.merge (Integer.Sparse.scale (2217492) (rows 13)) (Integer.Sparse.scale (13702404) (rows 14)) := by decide +kernel

theorem pairMergedZero10 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged10 x = 0 := by
  rw [pairMergeCheck10, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck11 : pairMerged11 = Integer.Sparse.merge pairMerged9 pairMerged10 := by decide +kernel

theorem pairMergedZero11 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged11 x = 0 := by
  rw [pairMergeCheck11, Integer.Sparse.eval_merge]
  rw [pairMergedZero9 x h, pairMergedZero10 x h]
  simp only [add_zero]

theorem pairMergeCheck12 : pairMerged12 = Integer.Sparse.merge pairMerged8 pairMerged11 := by decide +kernel

theorem pairMergedZero12 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged12 x = 0 := by
  rw [pairMergeCheck12, Integer.Sparse.eval_merge]
  rw [pairMergedZero8 x h, pairMergedZero11 x h]
  simp only [add_zero]

theorem pairMergeCheck13 : pairMerged13 = Integer.Sparse.merge pairMerged5 pairMerged12 := by decide +kernel

theorem pairMergedZero13 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged13 x = 0 := by
  rw [pairMergeCheck13, Integer.Sparse.eval_merge]
  rw [pairMergedZero5 x h, pairMergedZero12 x h]
  simp only [add_zero]

theorem pairMergeCheck14 : pairMerged14 = Integer.Sparse.merge (Integer.Sparse.scale (272160) (rows 15)) (Integer.Sparse.scale (8239054) (rows 16)) := by decide +kernel

theorem pairMergedZero14 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged14 x = 0 := by
  rw [pairMergeCheck14, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck15 : pairMerged15 = Integer.Sparse.merge (Integer.Sparse.scale (2019524) (rows 17)) (Integer.Sparse.scale (-10389192) (rows 18)) := by decide +kernel

theorem pairMergedZero15 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged15 x = 0 := by
  rw [pairMergeCheck15, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck16 : pairMerged16 = Integer.Sparse.merge pairMerged14 pairMerged15 := by decide +kernel

theorem pairMergedZero16 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged16 x = 0 := by
  rw [pairMergeCheck16, Integer.Sparse.eval_merge]
  rw [pairMergedZero14 x h, pairMergedZero15 x h]
  simp only [add_zero]

theorem pairMergeCheck17 : pairMerged17 = Integer.Sparse.merge (Integer.Sparse.scale (-32425890) (rows 19)) (Integer.Sparse.scale (-34128060) (rows 20)) := by decide +kernel

theorem pairMergedZero17 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged17 x = 0 := by
  rw [pairMergeCheck17, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck18 : pairMerged18 = Integer.Sparse.merge (Integer.Sparse.scale (7841304) (rows 21)) (Integer.Sparse.scale (5726176) (rows 22)) := by decide +kernel

theorem pairMergedZero18 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged18 x = 0 := by
  rw [pairMergeCheck18, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck19 : pairMerged19 = Integer.Sparse.merge pairMerged17 pairMerged18 := by decide +kernel

theorem pairMergedZero19 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged19 x = 0 := by
  rw [pairMergeCheck19, Integer.Sparse.eval_merge]
  rw [pairMergedZero17 x h, pairMergedZero18 x h]
  simp only [add_zero]

theorem pairMergeCheck20 : pairMerged20 = Integer.Sparse.merge pairMerged16 pairMerged19 := by decide +kernel

theorem pairMergedZero20 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged20 x = 0 := by
  rw [pairMergeCheck20, Integer.Sparse.eval_merge]
  rw [pairMergedZero16 x h, pairMergedZero19 x h]
  simp only [add_zero]

theorem pairMergeCheck21 : pairMerged21 = Integer.Sparse.merge (Integer.Sparse.scale (-8429664) (rows 23)) (Integer.Sparse.scale (-26590668) (rows 24)) := by decide +kernel

theorem pairMergedZero21 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged21 x = 0 := by
  rw [pairMergeCheck21, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck22 : pairMerged22 = Integer.Sparse.merge (Integer.Sparse.scale (6311934) (rows 25)) (Integer.Sparse.scale (1303428) (rows 26)) := by decide +kernel

theorem pairMergedZero22 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged22 x = 0 := by
  rw [pairMergeCheck22, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck23 : pairMerged23 = Integer.Sparse.merge pairMerged21 pairMerged22 := by decide +kernel

theorem pairMergedZero23 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged23 x = 0 := by
  rw [pairMergeCheck23, Integer.Sparse.eval_merge]
  rw [pairMergedZero21 x h, pairMergedZero22 x h]
  simp only [add_zero]

theorem pairMergeCheck24 : pairMerged24 = Integer.Sparse.merge (Integer.Sparse.scale (-12381870) (rows 27)) (Integer.Sparse.scale (1809816) (rows 28)) := by decide +kernel

theorem pairMergedZero24 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged24 x = 0 := by
  rw [pairMergeCheck24, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck25 : pairMerged25 = Integer.Sparse.merge (Integer.Sparse.scale (-3532032) (rows 29)) (Integer.Sparse.scale (1759104) (rows 30)) := by decide +kernel

theorem pairMergedZero25 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged25 x = 0 := by
  rw [pairMergeCheck25, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck26 : pairMerged26 = Integer.Sparse.merge pairMerged24 pairMerged25 := by decide +kernel

theorem pairMergedZero26 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged26 x = 0 := by
  rw [pairMergeCheck26, Integer.Sparse.eval_merge]
  rw [pairMergedZero24 x h, pairMergedZero25 x h]
  simp only [add_zero]

theorem pairMergeCheck27 : pairMerged27 = Integer.Sparse.merge pairMerged23 pairMerged26 := by decide +kernel

theorem pairMergedZero27 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged27 x = 0 := by
  rw [pairMergeCheck27, Integer.Sparse.eval_merge]
  rw [pairMergedZero23 x h, pairMergedZero26 x h]
  simp only [add_zero]

theorem pairMergeCheck28 : pairMerged28 = Integer.Sparse.merge pairMerged20 pairMerged27 := by decide +kernel

theorem pairMergedZero28 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged28 x = 0 := by
  rw [pairMergeCheck28, Integer.Sparse.eval_merge]
  rw [pairMergedZero20 x h, pairMergedZero27 x h]
  simp only [add_zero]

theorem pairMergeCheck29 : pairMerged29 = Integer.Sparse.merge pairMerged13 pairMerged28 := by decide +kernel

theorem pairMergedZero29 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged29 x = 0 := by
  rw [pairMergeCheck29, Integer.Sparse.eval_merge]
  rw [pairMergedZero13 x h, pairMergedZero28 x h]
  simp only [add_zero]

theorem pairMergeCheck30 : pairMerged30 = Integer.Sparse.merge (Integer.Sparse.scale (1485474) (rows 31)) (Integer.Sparse.scale (-15418944) (rows 32)) := by decide +kernel

theorem pairMergedZero30 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged30 x = 0 := by
  rw [pairMergeCheck30, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck31 : pairMerged31 = Integer.Sparse.merge (Integer.Sparse.scale (414486) (rows 33)) (Integer.Sparse.scale (-4520310) (rows 34)) := by decide +kernel

theorem pairMergedZero31 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged31 x = 0 := by
  rw [pairMergeCheck31, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck32 : pairMerged32 = Integer.Sparse.merge pairMerged30 pairMerged31 := by decide +kernel

theorem pairMergedZero32 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged32 x = 0 := by
  rw [pairMergeCheck32, Integer.Sparse.eval_merge]
  rw [pairMergedZero30 x h, pairMergedZero31 x h]
  simp only [add_zero]

theorem pairMergeCheck33 : pairMerged33 = Integer.Sparse.merge (Integer.Sparse.scale (-247200) (rows 35)) (Integer.Sparse.scale (1514052) (rows 36)) := by decide +kernel

theorem pairMergedZero33 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged33 x = 0 := by
  rw [pairMergeCheck33, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck34 : pairMerged34 = Integer.Sparse.merge (Integer.Sparse.scale (-6123420) (rows 37)) (Integer.Sparse.scale (1013760) (rows 38)) := by decide +kernel

theorem pairMergedZero34 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged34 x = 0 := by
  rw [pairMergeCheck34, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck35 : pairMerged35 = Integer.Sparse.merge pairMerged33 pairMerged34 := by decide +kernel

theorem pairMergedZero35 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged35 x = 0 := by
  rw [pairMergeCheck35, Integer.Sparse.eval_merge]
  rw [pairMergedZero33 x h, pairMergedZero34 x h]
  simp only [add_zero]

theorem pairMergeCheck36 : pairMerged36 = Integer.Sparse.merge pairMerged32 pairMerged35 := by decide +kernel

theorem pairMergedZero36 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged36 x = 0 := by
  rw [pairMergeCheck36, Integer.Sparse.eval_merge]
  rw [pairMergedZero32 x h, pairMergedZero35 x h]
  simp only [add_zero]

theorem pairMergeCheck37 : pairMerged37 = Integer.Sparse.merge (Integer.Sparse.scale (34256040) (rows 39)) (Integer.Sparse.scale (2978364) (rows 40)) := by decide +kernel

theorem pairMergedZero37 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged37 x = 0 := by
  rw [pairMergeCheck37, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck38 : pairMerged38 = Integer.Sparse.merge (Integer.Sparse.scale (-886821) (rows 41)) (Integer.Sparse.scale (-1082826) (rows 42)) := by decide +kernel

theorem pairMergedZero38 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged38 x = 0 := by
  rw [pairMergeCheck38, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck39 : pairMerged39 = Integer.Sparse.merge pairMerged37 pairMerged38 := by decide +kernel

theorem pairMergedZero39 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged39 x = 0 := by
  rw [pairMergeCheck39, Integer.Sparse.eval_merge]
  rw [pairMergedZero37 x h, pairMergedZero38 x h]
  simp only [add_zero]

theorem pairMergeCheck40 : pairMerged40 = Integer.Sparse.merge (Integer.Sparse.scale (3804132) (rows 43)) (Integer.Sparse.scale (-194472) (rows 44)) := by decide +kernel

theorem pairMergedZero40 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged40 x = 0 := by
  rw [pairMergeCheck40, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck41 : pairMerged41 = Integer.Sparse.merge (Integer.Sparse.scale (-141050) (rows 45)) (Integer.Sparse.scale (-294592) (rows 46)) := by decide +kernel

theorem pairMergedZero41 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged41 x = 0 := by
  rw [pairMergeCheck41, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck42 : pairMerged42 = Integer.Sparse.merge pairMerged40 pairMerged41 := by decide +kernel

theorem pairMergedZero42 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged42 x = 0 := by
  rw [pairMergeCheck42, Integer.Sparse.eval_merge]
  rw [pairMergedZero40 x h, pairMergedZero41 x h]
  simp only [add_zero]

theorem pairMergeCheck43 : pairMerged43 = Integer.Sparse.merge pairMerged39 pairMerged42 := by decide +kernel

theorem pairMergedZero43 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged43 x = 0 := by
  rw [pairMergeCheck43, Integer.Sparse.eval_merge]
  rw [pairMergedZero39 x h, pairMergedZero42 x h]
  simp only [add_zero]

theorem pairMergeCheck44 : pairMerged44 = Integer.Sparse.merge pairMerged36 pairMerged43 := by decide +kernel

theorem pairMergedZero44 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged44 x = 0 := by
  rw [pairMergeCheck44, Integer.Sparse.eval_merge]
  rw [pairMergedZero36 x h, pairMergedZero43 x h]
  simp only [add_zero]

theorem pairMergeCheck45 : pairMerged45 = Integer.Sparse.merge (Integer.Sparse.scale (-50028) (rows 47)) (Integer.Sparse.scale (-244776) (rows 48)) := by decide +kernel

theorem pairMergedZero45 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged45 x = 0 := by
  rw [pairMergeCheck45, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck46 : pairMerged46 = Integer.Sparse.merge (Integer.Sparse.scale (161104) (rows 49)) (Integer.Sparse.scale (269868) (rows 50)) := by decide +kernel

theorem pairMergedZero46 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged46 x = 0 := by
  rw [pairMergeCheck46, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck47 : pairMerged47 = Integer.Sparse.merge pairMerged45 pairMerged46 := by decide +kernel

theorem pairMergedZero47 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged47 x = 0 := by
  rw [pairMergeCheck47, Integer.Sparse.eval_merge]
  rw [pairMergedZero45 x h, pairMergedZero46 x h]
  simp only [add_zero]

theorem pairMergeCheck48 : pairMerged48 = Integer.Sparse.merge (Integer.Sparse.scale (-71544) (rows 51)) (Integer.Sparse.scale (105576) (rows 52)) := by decide +kernel

theorem pairMergedZero48 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged48 x = 0 := by
  rw [pairMergeCheck48, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck49 : pairMerged49 = Integer.Sparse.merge (Integer.Sparse.scale (-10490144) (rows 53)) (Integer.Sparse.scale (-790442) (rows 54)) := by decide +kernel

theorem pairMergedZero49 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged49 x = 0 := by
  rw [pairMergeCheck49, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck50 : pairMerged50 = Integer.Sparse.merge pairMerged48 pairMerged49 := by decide +kernel

theorem pairMergedZero50 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged50 x = 0 := by
  rw [pairMergeCheck50, Integer.Sparse.eval_merge]
  rw [pairMergedZero48 x h, pairMergedZero49 x h]
  simp only [add_zero]

theorem pairMergeCheck51 : pairMerged51 = Integer.Sparse.merge pairMerged47 pairMerged50 := by decide +kernel

theorem pairMergedZero51 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged51 x = 0 := by
  rw [pairMergeCheck51, Integer.Sparse.eval_merge]
  rw [pairMergedZero47 x h, pairMergedZero50 x h]
  simp only [add_zero]

theorem pairMergeCheck52 : pairMerged52 = Integer.Sparse.merge (Integer.Sparse.scale (595920) (rows 55)) (Integer.Sparse.scale (6912) (rows 56)) := by decide +kernel

theorem pairMergedZero52 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged52 x = 0 := by
  rw [pairMergeCheck52, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck53 : pairMerged53 = Integer.Sparse.merge (Integer.Sparse.scale (354960) (rows 57)) (Integer.Sparse.scale (887238) (rows 58)) := by decide +kernel

theorem pairMergedZero53 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged53 x = 0 := by
  rw [pairMergeCheck53, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck54 : pairMerged54 = Integer.Sparse.merge pairMerged52 pairMerged53 := by decide +kernel

theorem pairMergedZero54 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged54 x = 0 := by
  rw [pairMergeCheck54, Integer.Sparse.eval_merge]
  rw [pairMergedZero52 x h, pairMergedZero53 x h]
  simp only [add_zero]

theorem pairMergeCheck55 : pairMerged55 = Integer.Sparse.merge (Integer.Sparse.scale (9908820) (rows 59)) (Integer.Sparse.scale (2957200) (rows 60)) := by decide +kernel

theorem pairMergedZero55 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged55 x = 0 := by
  rw [pairMergeCheck55, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck56 : pairMerged56 = Integer.Sparse.merge (Integer.Sparse.scale (4519296) (rows 61)) (Integer.Sparse.scale (8476944) (rows 62)) := by decide +kernel

theorem pairMergedZero56 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged56 x = 0 := by
  rw [pairMergeCheck56, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck57 : pairMerged57 = Integer.Sparse.merge pairMerged55 pairMerged56 := by decide +kernel

theorem pairMergedZero57 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged57 x = 0 := by
  rw [pairMergeCheck57, Integer.Sparse.eval_merge]
  rw [pairMergedZero55 x h, pairMergedZero56 x h]
  simp only [add_zero]

theorem pairMergeCheck58 : pairMerged58 = Integer.Sparse.merge pairMerged54 pairMerged57 := by decide +kernel

theorem pairMergedZero58 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged58 x = 0 := by
  rw [pairMergeCheck58, Integer.Sparse.eval_merge]
  rw [pairMergedZero54 x h, pairMergedZero57 x h]
  simp only [add_zero]

theorem pairMergeCheck59 : pairMerged59 = Integer.Sparse.merge pairMerged51 pairMerged58 := by decide +kernel

theorem pairMergedZero59 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged59 x = 0 := by
  rw [pairMergeCheck59, Integer.Sparse.eval_merge]
  rw [pairMergedZero51 x h, pairMergedZero58 x h]
  simp only [add_zero]

theorem pairMergeCheck60 : pairMerged60 = Integer.Sparse.merge pairMerged44 pairMerged59 := by decide +kernel

theorem pairMergedZero60 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged60 x = 0 := by
  rw [pairMergeCheck60, Integer.Sparse.eval_merge]
  rw [pairMergedZero44 x h, pairMergedZero59 x h]
  simp only [add_zero]

theorem pairMergeCheck61 : pairMerged61 = Integer.Sparse.merge pairMerged29 pairMerged60 := by decide +kernel

theorem pairMergedZero61 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged61 x = 0 := by
  rw [pairMergeCheck61, Integer.Sparse.eval_merge]
  rw [pairMergedZero29 x h, pairMergedZero60 x h]
  simp only [add_zero]

theorem pairMergeCheck62 : pairMerged62 = Integer.Sparse.merge (Integer.Sparse.scale (6573480) (rows 63)) (Integer.Sparse.scale (5760) (rows 64)) := by decide +kernel

theorem pairMergedZero62 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged62 x = 0 := by
  rw [pairMergeCheck62, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck63 : pairMerged63 = Integer.Sparse.merge (Integer.Sparse.scale (-5653216) (rows 65)) (Integer.Sparse.scale (-172800) (rows 66)) := by decide +kernel

theorem pairMergedZero63 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged63 x = 0 := by
  rw [pairMergeCheck63, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck64 : pairMerged64 = Integer.Sparse.merge pairMerged62 pairMerged63 := by decide +kernel

theorem pairMergedZero64 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged64 x = 0 := by
  rw [pairMergeCheck64, Integer.Sparse.eval_merge]
  rw [pairMergedZero62 x h, pairMergedZero63 x h]
  simp only [add_zero]

theorem pairMergeCheck65 : pairMerged65 = Integer.Sparse.merge (Integer.Sparse.scale (744744) (rows 67)) (Integer.Sparse.scale (-13416360) (rows 68)) := by decide +kernel

theorem pairMergedZero65 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged65 x = 0 := by
  rw [pairMergeCheck65, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck66 : pairMerged66 = Integer.Sparse.merge (Integer.Sparse.scale (55338000) (rows 69)) (Integer.Sparse.scale (15840) (rows 70)) := by decide +kernel

theorem pairMergedZero66 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged66 x = 0 := by
  rw [pairMergeCheck66, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck67 : pairMerged67 = Integer.Sparse.merge pairMerged65 pairMerged66 := by decide +kernel

theorem pairMergedZero67 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged67 x = 0 := by
  rw [pairMergeCheck67, Integer.Sparse.eval_merge]
  rw [pairMergedZero65 x h, pairMergedZero66 x h]
  simp only [add_zero]

theorem pairMergeCheck68 : pairMerged68 = Integer.Sparse.merge pairMerged64 pairMerged67 := by decide +kernel

theorem pairMergedZero68 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged68 x = 0 := by
  rw [pairMergeCheck68, Integer.Sparse.eval_merge]
  rw [pairMergedZero64 x h, pairMergedZero67 x h]
  simp only [add_zero]

theorem pairMergeCheck69 : pairMerged69 = Integer.Sparse.merge (Integer.Sparse.scale (-553776) (rows 71)) (Integer.Sparse.scale (-834288) (rows 72)) := by decide +kernel

theorem pairMergedZero69 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged69 x = 0 := by
  rw [pairMergeCheck69, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck70 : pairMerged70 = Integer.Sparse.merge (Integer.Sparse.scale (-54336) (rows 73)) (Integer.Sparse.scale (418608) (rows 74)) := by decide +kernel

theorem pairMergedZero70 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged70 x = 0 := by
  rw [pairMergeCheck70, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck71 : pairMerged71 = Integer.Sparse.merge pairMerged69 pairMerged70 := by decide +kernel

theorem pairMergedZero71 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged71 x = 0 := by
  rw [pairMergeCheck71, Integer.Sparse.eval_merge]
  rw [pairMergedZero69 x h, pairMergedZero70 x h]
  simp only [add_zero]

theorem pairMergeCheck72 : pairMerged72 = Integer.Sparse.merge (Integer.Sparse.scale (1079268) (rows 75)) (Integer.Sparse.scale (-384918) (rows 76)) := by decide +kernel

theorem pairMergedZero72 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged72 x = 0 := by
  rw [pairMergeCheck72, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck73 : pairMerged73 = Integer.Sparse.merge (Integer.Sparse.scale (-2718705) (rows 77)) (Integer.Sparse.scale (-1041954) (rows 78)) := by decide +kernel

theorem pairMergedZero73 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged73 x = 0 := by
  rw [pairMergeCheck73, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck74 : pairMerged74 = Integer.Sparse.merge pairMerged72 pairMerged73 := by decide +kernel

theorem pairMergedZero74 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged74 x = 0 := by
  rw [pairMergeCheck74, Integer.Sparse.eval_merge]
  rw [pairMergedZero72 x h, pairMergedZero73 x h]
  simp only [add_zero]

theorem pairMergeCheck75 : pairMerged75 = Integer.Sparse.merge pairMerged71 pairMerged74 := by decide +kernel

theorem pairMergedZero75 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged75 x = 0 := by
  rw [pairMergeCheck75, Integer.Sparse.eval_merge]
  rw [pairMergedZero71 x h, pairMergedZero74 x h]
  simp only [add_zero]

theorem pairMergeCheck76 : pairMerged76 = Integer.Sparse.merge pairMerged68 pairMerged75 := by decide +kernel

theorem pairMergedZero76 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged76 x = 0 := by
  rw [pairMergeCheck76, Integer.Sparse.eval_merge]
  rw [pairMergedZero68 x h, pairMergedZero75 x h]
  simp only [add_zero]

theorem pairMergeCheck77 : pairMerged77 = Integer.Sparse.merge (Integer.Sparse.scale (5152170) (rows 79)) (Integer.Sparse.scale (5087700) (rows 80)) := by decide +kernel

theorem pairMergedZero77 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged77 x = 0 := by
  rw [pairMergeCheck77, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck78 : pairMerged78 = Integer.Sparse.merge (Integer.Sparse.scale (-11211255) (rows 81)) (Integer.Sparse.scale (420270) (rows 82)) := by decide +kernel

theorem pairMergedZero78 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged78 x = 0 := by
  rw [pairMergeCheck78, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck79 : pairMerged79 = Integer.Sparse.merge pairMerged77 pairMerged78 := by decide +kernel

theorem pairMergedZero79 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged79 x = 0 := by
  rw [pairMergeCheck79, Integer.Sparse.eval_merge]
  rw [pairMergedZero77 x h, pairMergedZero78 x h]
  simp only [add_zero]

theorem pairMergeCheck80 : pairMerged80 = Integer.Sparse.merge (Integer.Sparse.scale (2334468) (rows 83)) (Integer.Sparse.scale (-1483974) (rows 84)) := by decide +kernel

theorem pairMergedZero80 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged80 x = 0 := by
  rw [pairMergeCheck80, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck81 : pairMerged81 = Integer.Sparse.merge (Integer.Sparse.scale (-2766900) (rows 85)) (Integer.Sparse.scale (1656948) (rows 86)) := by decide +kernel

theorem pairMergedZero81 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged81 x = 0 := by
  rw [pairMergeCheck81, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck82 : pairMerged82 = Integer.Sparse.merge pairMerged80 pairMerged81 := by decide +kernel

theorem pairMergedZero82 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged82 x = 0 := by
  rw [pairMergeCheck82, Integer.Sparse.eval_merge]
  rw [pairMergedZero80 x h, pairMergedZero81 x h]
  simp only [add_zero]

theorem pairMergeCheck83 : pairMerged83 = Integer.Sparse.merge pairMerged79 pairMerged82 := by decide +kernel

theorem pairMergedZero83 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged83 x = 0 := by
  rw [pairMergeCheck83, Integer.Sparse.eval_merge]
  rw [pairMergedZero79 x h, pairMergedZero82 x h]
  simp only [add_zero]

theorem pairMergeCheck84 : pairMerged84 = Integer.Sparse.merge (Integer.Sparse.scale (1109952) (rows 87)) (Integer.Sparse.scale (32256) (rows 88)) := by decide +kernel

theorem pairMergedZero84 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged84 x = 0 := by
  rw [pairMergeCheck84, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck85 : pairMerged85 = Integer.Sparse.merge (Integer.Sparse.scale (2886132) (rows 89)) (Integer.Sparse.scale (924096) (rows 90)) := by decide +kernel

theorem pairMergedZero85 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged85 x = 0 := by
  rw [pairMergeCheck85, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck86 : pairMerged86 = Integer.Sparse.merge pairMerged84 pairMerged85 := by decide +kernel

theorem pairMergedZero86 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged86 x = 0 := by
  rw [pairMergeCheck86, Integer.Sparse.eval_merge]
  rw [pairMergedZero84 x h, pairMergedZero85 x h]
  simp only [add_zero]

theorem pairMergeCheck87 : pairMerged87 = Integer.Sparse.merge (Integer.Sparse.scale (-615396) (rows 91)) (Integer.Sparse.scale (-126732) (rows 92)) := by decide +kernel

theorem pairMergedZero87 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged87 x = 0 := by
  rw [pairMergeCheck87, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck88 : pairMerged88 = Integer.Sparse.merge (Integer.Sparse.scale (-4136592) (rows 93)) (Integer.Sparse.scale (77280) (rows 94)) := by decide +kernel

theorem pairMergedZero88 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged88 x = 0 := by
  rw [pairMergeCheck88, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck89 : pairMerged89 = Integer.Sparse.merge pairMerged87 pairMerged88 := by decide +kernel

theorem pairMergedZero89 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged89 x = 0 := by
  rw [pairMergeCheck89, Integer.Sparse.eval_merge]
  rw [pairMergedZero87 x h, pairMergedZero88 x h]
  simp only [add_zero]

theorem pairMergeCheck90 : pairMerged90 = Integer.Sparse.merge pairMerged86 pairMerged89 := by decide +kernel

theorem pairMergedZero90 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged90 x = 0 := by
  rw [pairMergeCheck90, Integer.Sparse.eval_merge]
  rw [pairMergedZero86 x h, pairMergedZero89 x h]
  simp only [add_zero]

theorem pairMergeCheck91 : pairMerged91 = Integer.Sparse.merge pairMerged83 pairMerged90 := by decide +kernel

theorem pairMergedZero91 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged91 x = 0 := by
  rw [pairMergeCheck91, Integer.Sparse.eval_merge]
  rw [pairMergedZero83 x h, pairMergedZero90 x h]
  simp only [add_zero]

theorem pairMergeCheck92 : pairMerged92 = Integer.Sparse.merge pairMerged76 pairMerged91 := by decide +kernel

theorem pairMergedZero92 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged92 x = 0 := by
  rw [pairMergeCheck92, Integer.Sparse.eval_merge]
  rw [pairMergedZero76 x h, pairMergedZero91 x h]
  simp only [add_zero]

theorem pairMergeCheck93 : pairMerged93 = Integer.Sparse.merge (Integer.Sparse.scale (78720) (rows 95)) (Integer.Sparse.scale (-1950240) (rows 96)) := by decide +kernel

theorem pairMergedZero93 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged93 x = 0 := by
  rw [pairMergeCheck93, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck94 : pairMerged94 = Integer.Sparse.merge (Integer.Sparse.scale (-3304992) (rows 97)) (Integer.Sparse.scale (5108970) (rows 98)) := by decide +kernel

theorem pairMergedZero94 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged94 x = 0 := by
  rw [pairMergeCheck94, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck95 : pairMerged95 = Integer.Sparse.merge pairMerged93 pairMerged94 := by decide +kernel

theorem pairMergedZero95 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged95 x = 0 := by
  rw [pairMergeCheck95, Integer.Sparse.eval_merge]
  rw [pairMergedZero93 x h, pairMergedZero94 x h]
  simp only [add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck96 : pairMerged96 = Integer.Sparse.merge (Integer.Sparse.scale (-1895688) (rows 99)) (Integer.Sparse.scale (1575780) (rows 100)) := by decide +kernel

theorem pairMergedZero96 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged96 x = 0 := by
  rw [pairMergeCheck96, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck97 : pairMerged97 = Integer.Sparse.merge (Integer.Sparse.scale (-3014980) (rows 101)) (Integer.Sparse.scale (466212) (rows 102)) := by decide +kernel

theorem pairMergedZero97 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged97 x = 0 := by
  rw [pairMergeCheck97, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck98 : pairMerged98 = Integer.Sparse.merge pairMerged96 pairMerged97 := by decide +kernel

theorem pairMergedZero98 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged98 x = 0 := by
  rw [pairMergeCheck98, Integer.Sparse.eval_merge]
  rw [pairMergedZero96 x h, pairMergedZero97 x h]
  simp only [add_zero]

theorem pairMergeCheck99 : pairMerged99 = Integer.Sparse.merge pairMerged95 pairMerged98 := by decide +kernel

theorem pairMergedZero99 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged99 x = 0 := by
  rw [pairMergeCheck99, Integer.Sparse.eval_merge]
  rw [pairMergedZero95 x h, pairMergedZero98 x h]
  simp only [add_zero]

theorem pairMergeCheck100 : pairMerged100 = Integer.Sparse.merge (Integer.Sparse.scale (51084) (rows 103)) (Integer.Sparse.scale (31056) (rows 104)) := by decide +kernel

theorem pairMergedZero100 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged100 x = 0 := by
  rw [pairMergeCheck100, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck101 : pairMerged101 = Integer.Sparse.merge (Integer.Sparse.scale (1228320) (rows 105)) (Integer.Sparse.scale (2016) (rows 106)) := by decide +kernel

theorem pairMergedZero101 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged101 x = 0 := by
  rw [pairMergeCheck101, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck102 : pairMerged102 = Integer.Sparse.merge pairMerged100 pairMerged101 := by decide +kernel

theorem pairMergedZero102 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged102 x = 0 := by
  rw [pairMergeCheck102, Integer.Sparse.eval_merge]
  rw [pairMergedZero100 x h, pairMergedZero101 x h]
  simp only [add_zero]

theorem pairMergeCheck103 : pairMerged103 = Integer.Sparse.merge (Integer.Sparse.scale (-40764) (rows 107)) (Integer.Sparse.scale (91728) (rows 108)) := by decide +kernel

theorem pairMergedZero103 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged103 x = 0 := by
  rw [pairMergeCheck103, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck104 : pairMerged104 = Integer.Sparse.merge (Integer.Sparse.scale (-147528) (rows 109)) (Integer.Sparse.scale (-100152) (rows 110)) := by decide +kernel

theorem pairMergedZero104 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged104 x = 0 := by
  rw [pairMergeCheck104, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck105 : pairMerged105 = Integer.Sparse.merge pairMerged103 pairMerged104 := by decide +kernel

theorem pairMergedZero105 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged105 x = 0 := by
  rw [pairMergeCheck105, Integer.Sparse.eval_merge]
  rw [pairMergedZero103 x h, pairMergedZero104 x h]
  simp only [add_zero]

theorem pairMergeCheck106 : pairMerged106 = Integer.Sparse.merge pairMerged102 pairMerged105 := by decide +kernel

theorem pairMergedZero106 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged106 x = 0 := by
  rw [pairMergeCheck106, Integer.Sparse.eval_merge]
  rw [pairMergedZero102 x h, pairMergedZero105 x h]
  simp only [add_zero]

theorem pairMergeCheck107 : pairMerged107 = Integer.Sparse.merge pairMerged99 pairMerged106 := by decide +kernel

theorem pairMergedZero107 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged107 x = 0 := by
  rw [pairMergeCheck107, Integer.Sparse.eval_merge]
  rw [pairMergedZero99 x h, pairMergedZero106 x h]
  simp only [add_zero]

theorem pairMergeCheck108 : pairMerged108 = Integer.Sparse.merge (Integer.Sparse.scale (-255360) (rows 111)) (Integer.Sparse.scale (81528) (rows 112)) := by decide +kernel

theorem pairMergedZero108 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged108 x = 0 := by
  rw [pairMergeCheck108, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck109 : pairMerged109 = Integer.Sparse.merge (Integer.Sparse.scale (-408240) (rows 113)) (Integer.Sparse.scale (156276) (rows 114)) := by decide +kernel

theorem pairMergedZero109 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged109 x = 0 := by
  rw [pairMergeCheck109, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck110 : pairMerged110 = Integer.Sparse.merge pairMerged108 pairMerged109 := by decide +kernel

theorem pairMergedZero110 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged110 x = 0 := by
  rw [pairMergeCheck110, Integer.Sparse.eval_merge]
  rw [pairMergedZero108 x h, pairMergedZero109 x h]
  simp only [add_zero]

theorem pairMergeCheck111 : pairMerged111 = Integer.Sparse.merge (Integer.Sparse.scale (-52812) (rows 115)) (Integer.Sparse.scale (283392) (rows 116)) := by decide +kernel

theorem pairMergedZero111 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged111 x = 0 := by
  rw [pairMergeCheck111, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck112 : pairMerged112 = Integer.Sparse.merge (Integer.Sparse.scale (-83664) (rows 117)) (Integer.Sparse.scale (-571680) (rows 118)) := by decide +kernel

theorem pairMergedZero112 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged112 x = 0 := by
  rw [pairMergeCheck112, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck113 : pairMerged113 = Integer.Sparse.merge pairMerged111 pairMerged112 := by decide +kernel

theorem pairMergedZero113 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged113 x = 0 := by
  rw [pairMergeCheck113, Integer.Sparse.eval_merge]
  rw [pairMergedZero111 x h, pairMergedZero112 x h]
  simp only [add_zero]

theorem pairMergeCheck114 : pairMerged114 = Integer.Sparse.merge pairMerged110 pairMerged113 := by decide +kernel

theorem pairMergedZero114 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged114 x = 0 := by
  rw [pairMergeCheck114, Integer.Sparse.eval_merge]
  rw [pairMergedZero110 x h, pairMergedZero113 x h]
  simp only [add_zero]

theorem pairMergeCheck115 : pairMerged115 = Integer.Sparse.merge (Integer.Sparse.scale (-57312) (rows 119)) (Integer.Sparse.scale (463104) (rows 120)) := by decide +kernel

theorem pairMergedZero115 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged115 x = 0 := by
  rw [pairMergeCheck115, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck116 : pairMerged116 = Integer.Sparse.merge (Integer.Sparse.scale (6912) (rows 121)) (Integer.Sparse.scale (9216) (rows 122)) := by decide +kernel

theorem pairMergedZero116 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged116 x = 0 := by
  rw [pairMergeCheck116, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck117 : pairMerged117 = Integer.Sparse.merge pairMerged115 pairMerged116 := by decide +kernel

theorem pairMergedZero117 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged117 x = 0 := by
  rw [pairMergeCheck117, Integer.Sparse.eval_merge]
  rw [pairMergedZero115 x h, pairMergedZero116 x h]
  simp only [add_zero]

theorem pairMergeCheck118 : pairMerged118 = Integer.Sparse.merge (Integer.Sparse.scale (22032) (rows 123)) (Integer.Sparse.scale (237600) (rows 124)) := by decide +kernel

theorem pairMergedZero118 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged118 x = 0 := by
  rw [pairMergeCheck118, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck119 : pairMerged119 = Integer.Sparse.merge (Integer.Sparse.scale (83664) (rows 125)) (Integer.Sparse.scale (-91728) (rows 126)) := by decide +kernel

theorem pairMergedZero119 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged119 x = 0 := by
  rw [pairMergeCheck119, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck120 : pairMerged120 = Integer.Sparse.merge pairMerged118 pairMerged119 := by decide +kernel

theorem pairMergedZero120 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged120 x = 0 := by
  rw [pairMergeCheck120, Integer.Sparse.eval_merge]
  rw [pairMergedZero118 x h, pairMergedZero119 x h]
  simp only [add_zero]

theorem pairMergeCheck121 : pairMerged121 = Integer.Sparse.merge pairMerged117 pairMerged120 := by decide +kernel

theorem pairMergedZero121 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged121 x = 0 := by
  rw [pairMergeCheck121, Integer.Sparse.eval_merge]
  rw [pairMergedZero117 x h, pairMergedZero120 x h]
  simp only [add_zero]

theorem pairMergeCheck122 : pairMerged122 = Integer.Sparse.merge pairMerged114 pairMerged121 := by decide +kernel

theorem pairMergedZero122 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged122 x = 0 := by
  rw [pairMergeCheck122, Integer.Sparse.eval_merge]
  rw [pairMergedZero114 x h, pairMergedZero121 x h]
  simp only [add_zero]

theorem pairMergeCheck123 : pairMerged123 = Integer.Sparse.merge pairMerged107 pairMerged122 := by decide +kernel

theorem pairMergedZero123 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged123 x = 0 := by
  rw [pairMergeCheck123, Integer.Sparse.eval_merge]
  rw [pairMergedZero107 x h, pairMergedZero122 x h]
  simp only [add_zero]

theorem pairMergeCheck124 : pairMerged124 = Integer.Sparse.merge pairMerged92 pairMerged123 := by decide +kernel

theorem pairMergedZero124 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged124 x = 0 := by
  rw [pairMergeCheck124, Integer.Sparse.eval_merge]
  rw [pairMergedZero92 x h, pairMergedZero123 x h]
  simp only [add_zero]

theorem pairMergeCheck125 : pairMerged125 = Integer.Sparse.merge pairMerged61 pairMerged124 := by decide +kernel

theorem pairMergedZero125 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged125 x = 0 := by
  rw [pairMergeCheck125, Integer.Sparse.eval_merge]
  rw [pairMergedZero61 x h, pairMergedZero124 x h]
  simp only [add_zero]

theorem pairMergeCheck126 : pairMerged126 = Integer.Sparse.merge (Integer.Sparse.scale (-220032) (rows 127)) (Integer.Sparse.scale (1024200) (rows 128)) := by decide +kernel

theorem pairMergedZero126 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged126 x = 0 := by
  rw [pairMergeCheck126, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck127 : pairMerged127 = Integer.Sparse.merge (Integer.Sparse.scale (-1024200) (rows 129)) (Integer.Sparse.scale (-56160) (rows 130)) := by decide +kernel

theorem pairMergedZero127 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged127 x = 0 := by
  rw [pairMergeCheck127, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck128 : pairMerged128 = Integer.Sparse.merge pairMerged126 pairMerged127 := by decide +kernel

theorem pairMergedZero128 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged128 x = 0 := by
  rw [pairMergeCheck128, Integer.Sparse.eval_merge]
  rw [pairMergedZero126 x h, pairMergedZero127 x h]
  simp only [add_zero]

theorem pairMergeCheck129 : pairMerged129 = Integer.Sparse.merge (Integer.Sparse.scale (163872) (rows 131)) (Integer.Sparse.scale (11520) (rows 132)) := by decide +kernel

theorem pairMergedZero129 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged129 x = 0 := by
  rw [pairMergeCheck129, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck130 : pairMerged130 = Integer.Sparse.merge (Integer.Sparse.scale (-49536) (rows 133)) (Integer.Sparse.scale (-51840) (rows 134)) := by decide +kernel

theorem pairMergedZero130 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged130 x = 0 := by
  rw [pairMergeCheck130, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck131 : pairMerged131 = Integer.Sparse.merge pairMerged129 pairMerged130 := by decide +kernel

theorem pairMergedZero131 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged131 x = 0 := by
  rw [pairMergeCheck131, Integer.Sparse.eval_merge]
  rw [pairMergedZero129 x h, pairMergedZero130 x h]
  simp only [add_zero]

theorem pairMergeCheck132 : pairMerged132 = Integer.Sparse.merge pairMerged128 pairMerged131 := by decide +kernel

theorem pairMergedZero132 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged132 x = 0 := by
  rw [pairMergeCheck132, Integer.Sparse.eval_merge]
  rw [pairMergedZero128 x h, pairMergedZero131 x h]
  simp only [add_zero]

theorem pairMergeCheck133 : pairMerged133 = Integer.Sparse.merge (Integer.Sparse.scale (83880) (rows 135)) (Integer.Sparse.scale (44064) (rows 136)) := by decide +kernel

theorem pairMergedZero133 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged133 x = 0 := by
  rw [pairMergeCheck133, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck134 : pairMerged134 = Integer.Sparse.merge (Integer.Sparse.scale (80640) (rows 137)) (Integer.Sparse.scale (134328) (rows 138)) := by decide +kernel

theorem pairMergedZero134 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged134 x = 0 := by
  rw [pairMergeCheck134, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck135 : pairMerged135 = Integer.Sparse.merge pairMerged133 pairMerged134 := by decide +kernel

theorem pairMergedZero135 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged135 x = 0 := by
  rw [pairMergeCheck135, Integer.Sparse.eval_merge]
  rw [pairMergedZero133 x h, pairMergedZero134 x h]
  simp only [add_zero]

theorem pairMergeCheck136 : pairMerged136 = Integer.Sparse.merge (Integer.Sparse.scale (-36984) (rows 139)) (Integer.Sparse.scale (-7200) (rows 140)) := by decide +kernel

theorem pairMergedZero136 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged136 x = 0 := by
  rw [pairMergeCheck136, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck137 : pairMerged137 = Integer.Sparse.merge (Integer.Sparse.scale (-72936) (rows 141)) (Integer.Sparse.scale (116424) (rows 142)) := by decide +kernel

theorem pairMergedZero137 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged137 x = 0 := by
  rw [pairMergeCheck137, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck138 : pairMerged138 = Integer.Sparse.merge pairMerged136 pairMerged137 := by decide +kernel

theorem pairMergedZero138 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged138 x = 0 := by
  rw [pairMergeCheck138, Integer.Sparse.eval_merge]
  rw [pairMergedZero136 x h, pairMergedZero137 x h]
  simp only [add_zero]

theorem pairMergeCheck139 : pairMerged139 = Integer.Sparse.merge pairMerged135 pairMerged138 := by decide +kernel

theorem pairMergedZero139 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged139 x = 0 := by
  rw [pairMergeCheck139, Integer.Sparse.eval_merge]
  rw [pairMergedZero135 x h, pairMergedZero138 x h]
  simp only [add_zero]

theorem pairMergeCheck140 : pairMerged140 = Integer.Sparse.merge pairMerged132 pairMerged139 := by decide +kernel

theorem pairMergedZero140 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged140 x = 0 := by
  rw [pairMergeCheck140, Integer.Sparse.eval_merge]
  rw [pairMergedZero132 x h, pairMergedZero139 x h]
  simp only [add_zero]

theorem pairMergeCheck141 : pairMerged141 = Integer.Sparse.merge (Integer.Sparse.scale (-95688) (rows 143)) (Integer.Sparse.scale (55728) (rows 144)) := by decide +kernel

theorem pairMergedZero141 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged141 x = 0 := by
  rw [pairMergeCheck141, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck142 : pairMerged142 = Integer.Sparse.merge (Integer.Sparse.scale (-17280) (rows 145)) (Integer.Sparse.scale (-217152) (rows 146)) := by decide +kernel

theorem pairMergedZero142 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged142 x = 0 := by
  rw [pairMergeCheck142, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck143 : pairMerged143 = Integer.Sparse.merge pairMerged141 pairMerged142 := by decide +kernel

theorem pairMergedZero143 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged143 x = 0 := by
  rw [pairMergeCheck143, Integer.Sparse.eval_merge]
  rw [pairMergedZero141 x h, pairMergedZero142 x h]
  simp only [add_zero]

theorem pairMergeCheck144 : pairMerged144 = Integer.Sparse.merge (Integer.Sparse.scale (-41904) (rows 147)) (Integer.Sparse.scale (-62496) (rows 148)) := by decide +kernel

theorem pairMergedZero144 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged144 x = 0 := by
  rw [pairMergeCheck144, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck145 : pairMerged145 = Integer.Sparse.merge (Integer.Sparse.scale (420480) (rows 149)) (Integer.Sparse.scale (53568) (rows 150)) := by decide +kernel

theorem pairMergedZero145 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged145 x = 0 := by
  rw [pairMergeCheck145, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck146 : pairMerged146 = Integer.Sparse.merge pairMerged144 pairMerged145 := by decide +kernel

theorem pairMergedZero146 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged146 x = 0 := by
  rw [pairMergeCheck146, Integer.Sparse.eval_merge]
  rw [pairMergedZero144 x h, pairMergedZero145 x h]
  simp only [add_zero]

theorem pairMergeCheck147 : pairMerged147 = Integer.Sparse.merge pairMerged143 pairMerged146 := by decide +kernel

theorem pairMergedZero147 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged147 x = 0 := by
  rw [pairMergeCheck147, Integer.Sparse.eval_merge]
  rw [pairMergedZero143 x h, pairMergedZero146 x h]
  simp only [add_zero]

theorem pairMergeCheck148 : pairMerged148 = Integer.Sparse.merge (Integer.Sparse.scale (-10368) (rows 151)) (Integer.Sparse.scale (-221760) (rows 152)) := by decide +kernel

theorem pairMergedZero148 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged148 x = 0 := by
  rw [pairMergeCheck148, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck149 : pairMerged149 = Integer.Sparse.merge (Integer.Sparse.scale (-17856) (rows 153)) (Integer.Sparse.scale (-76968) (rows 154)) := by decide +kernel

theorem pairMergedZero149 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged149 x = 0 := by
  rw [pairMergeCheck149, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck150 : pairMerged150 = Integer.Sparse.merge pairMerged148 pairMerged149 := by decide +kernel

theorem pairMergedZero150 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged150 x = 0 := by
  rw [pairMergeCheck150, Integer.Sparse.eval_merge]
  rw [pairMergedZero148 x h, pairMergedZero149 x h]
  simp only [add_zero]

theorem pairMergeCheck151 : pairMerged151 = Integer.Sparse.merge (Integer.Sparse.scale (76968) (rows 155)) (Integer.Sparse.scale (17856) (rows 156)) := by decide +kernel

theorem pairMergedZero151 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged151 x = 0 := by
  rw [pairMergeCheck151, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck152 : pairMerged152 = Integer.Sparse.merge (Integer.Sparse.scale (-229680) (rows 157)) (Integer.Sparse.scale (81504) (rows 158)) := by decide +kernel

theorem pairMergedZero152 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged152 x = 0 := by
  rw [pairMergeCheck152, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck153 : pairMerged153 = Integer.Sparse.merge pairMerged151 pairMerged152 := by decide +kernel

theorem pairMergedZero153 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged153 x = 0 := by
  rw [pairMergeCheck153, Integer.Sparse.eval_merge]
  rw [pairMergedZero151 x h, pairMergedZero152 x h]
  simp only [add_zero]

theorem pairMergeCheck154 : pairMerged154 = Integer.Sparse.merge pairMerged150 pairMerged153 := by decide +kernel

theorem pairMergedZero154 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged154 x = 0 := by
  rw [pairMergeCheck154, Integer.Sparse.eval_merge]
  rw [pairMergedZero150 x h, pairMergedZero153 x h]
  simp only [add_zero]

theorem pairMergeCheck155 : pairMerged155 = Integer.Sparse.merge pairMerged147 pairMerged154 := by decide +kernel

theorem pairMergedZero155 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged155 x = 0 := by
  rw [pairMergeCheck155, Integer.Sparse.eval_merge]
  rw [pairMergedZero147 x h, pairMergedZero154 x h]
  simp only [add_zero]

theorem pairMergeCheck156 : pairMerged156 = Integer.Sparse.merge pairMerged140 pairMerged155 := by decide +kernel

theorem pairMergedZero156 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged156 x = 0 := by
  rw [pairMergeCheck156, Integer.Sparse.eval_merge]
  rw [pairMergedZero140 x h, pairMergedZero155 x h]
  simp only [add_zero]

theorem pairMergeCheck157 : pairMerged157 = Integer.Sparse.merge (Integer.Sparse.scale (-338880) (rows 159)) (Integer.Sparse.scale (-34048) (rows 160)) := by decide +kernel

theorem pairMergedZero157 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged157 x = 0 := by
  rw [pairMergeCheck157, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck158 : pairMerged158 = Integer.Sparse.merge (Integer.Sparse.scale (11520) (rows 161)) (Integer.Sparse.scale (1920) (rows 162)) := by decide +kernel

theorem pairMergedZero158 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged158 x = 0 := by
  rw [pairMergeCheck158, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck159 : pairMerged159 = Integer.Sparse.merge pairMerged157 pairMerged158 := by decide +kernel

theorem pairMergedZero159 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged159 x = 0 := by
  rw [pairMergeCheck159, Integer.Sparse.eval_merge]
  rw [pairMergedZero157 x h, pairMergedZero158 x h]
  simp only [add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck160 : pairMerged160 = Integer.Sparse.merge (Integer.Sparse.scale (-5760) (rows 163)) (Integer.Sparse.scale (-34560) (rows 164)) := by decide +kernel

theorem pairMergedZero160 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged160 x = 0 := by
  rw [pairMergeCheck160, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck161 : pairMerged161 = Integer.Sparse.merge (Integer.Sparse.scale (10080) (rows 165)) (Integer.Sparse.scale (-28440) (rows 166)) := by decide +kernel

theorem pairMergedZero161 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged161 x = 0 := by
  rw [pairMergeCheck161, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck162 : pairMerged162 = Integer.Sparse.merge pairMerged160 pairMerged161 := by decide +kernel

theorem pairMergedZero162 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged162 x = 0 := by
  rw [pairMergeCheck162, Integer.Sparse.eval_merge]
  rw [pairMergedZero160 x h, pairMergedZero161 x h]
  simp only [add_zero]

theorem pairMergeCheck163 : pairMerged163 = Integer.Sparse.merge pairMerged159 pairMerged162 := by decide +kernel

theorem pairMergedZero163 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged163 x = 0 := by
  rw [pairMergeCheck163, Integer.Sparse.eval_merge]
  rw [pairMergedZero159 x h, pairMergedZero162 x h]
  simp only [add_zero]

theorem pairMergeCheck164 : pairMerged164 = Integer.Sparse.merge (Integer.Sparse.scale (-12096) (rows 167)) (Integer.Sparse.scale (-79200) (rows 168)) := by decide +kernel

theorem pairMergedZero164 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged164 x = 0 := by
  rw [pairMergeCheck164, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck165 : pairMerged165 = Integer.Sparse.merge (Integer.Sparse.scale (-84960) (rows 169)) (Integer.Sparse.scale (-576) (rows 170)) := by decide +kernel

theorem pairMergedZero165 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged165 x = 0 := by
  rw [pairMergeCheck165, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck166 : pairMerged166 = Integer.Sparse.merge pairMerged164 pairMerged165 := by decide +kernel

theorem pairMergedZero166 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged166 x = 0 := by
  rw [pairMergeCheck166, Integer.Sparse.eval_merge]
  rw [pairMergedZero164 x h, pairMergedZero165 x h]
  simp only [add_zero]

theorem pairMergeCheck167 : pairMerged167 = Integer.Sparse.merge (Integer.Sparse.scale (10656) (rows 171)) (Integer.Sparse.scale (12960) (rows 172)) := by decide +kernel

theorem pairMergedZero167 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged167 x = 0 := by
  rw [pairMergeCheck167, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck168 : pairMerged168 = Integer.Sparse.merge (Integer.Sparse.scale (10656) (rows 173)) (Integer.Sparse.scale (-97416) (rows 174)) := by decide +kernel

theorem pairMergedZero168 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged168 x = 0 := by
  rw [pairMergeCheck168, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck169 : pairMerged169 = Integer.Sparse.merge pairMerged167 pairMerged168 := by decide +kernel

theorem pairMergedZero169 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged169 x = 0 := by
  rw [pairMergeCheck169, Integer.Sparse.eval_merge]
  rw [pairMergedZero167 x h, pairMergedZero168 x h]
  simp only [add_zero]

theorem pairMergeCheck170 : pairMerged170 = Integer.Sparse.merge pairMerged166 pairMerged169 := by decide +kernel

theorem pairMergedZero170 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged170 x = 0 := by
  rw [pairMergeCheck170, Integer.Sparse.eval_merge]
  rw [pairMergedZero166 x h, pairMergedZero169 x h]
  simp only [add_zero]

theorem pairMergeCheck171 : pairMerged171 = Integer.Sparse.merge pairMerged163 pairMerged170 := by decide +kernel

theorem pairMergedZero171 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged171 x = 0 := by
  rw [pairMergeCheck171, Integer.Sparse.eval_merge]
  rw [pairMergedZero163 x h, pairMergedZero170 x h]
  simp only [add_zero]

theorem pairMergeCheck172 : pairMerged172 = Integer.Sparse.merge (Integer.Sparse.scale (-78408) (rows 175)) (Integer.Sparse.scale (487080) (rows 176)) := by decide +kernel

theorem pairMergedZero172 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged172 x = 0 := by
  rw [pairMergeCheck172, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck173 : pairMerged173 = Integer.Sparse.merge (Integer.Sparse.scale (78408) (rows 177)) (Integer.Sparse.scale (-15840) (rows 178)) := by decide +kernel

theorem pairMergedZero173 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged173 x = 0 := by
  rw [pairMergeCheck173, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck174 : pairMerged174 = Integer.Sparse.merge pairMerged172 pairMerged173 := by decide +kernel

theorem pairMergedZero174 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged174 x = 0 := by
  rw [pairMergeCheck174, Integer.Sparse.eval_merge]
  rw [pairMergedZero172 x h, pairMergedZero173 x h]
  simp only [add_zero]

theorem pairMergeCheck175 : pairMerged175 = Integer.Sparse.merge (Integer.Sparse.scale (15840) (rows 179)) (Integer.Sparse.scale (136080) (rows 180)) := by decide +kernel

theorem pairMergedZero175 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged175 x = 0 := by
  rw [pairMergeCheck175, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck176 : pairMerged176 = Integer.Sparse.merge (Integer.Sparse.scale (5760) (rows 181)) (Integer.Sparse.scale (-6336) (rows 182)) := by decide +kernel

theorem pairMergedZero176 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged176 x = 0 := by
  rw [pairMergeCheck176, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck177 : pairMerged177 = Integer.Sparse.merge pairMerged175 pairMerged176 := by decide +kernel

theorem pairMergedZero177 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged177 x = 0 := by
  rw [pairMergeCheck177, Integer.Sparse.eval_merge]
  rw [pairMergedZero175 x h, pairMergedZero176 x h]
  simp only [add_zero]

theorem pairMergeCheck178 : pairMerged178 = Integer.Sparse.merge pairMerged174 pairMerged177 := by decide +kernel

theorem pairMergedZero178 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged178 x = 0 := by
  rw [pairMergeCheck178, Integer.Sparse.eval_merge]
  rw [pairMergedZero174 x h, pairMergedZero177 x h]
  simp only [add_zero]

theorem pairMergeCheck179 : pairMerged179 = Integer.Sparse.merge (Integer.Sparse.scale (30880) (rows 183)) (Integer.Sparse.scale (1696) (rows 184)) := by decide +kernel

theorem pairMergedZero179 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged179 x = 0 := by
  rw [pairMergeCheck179, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck180 : pairMerged180 = Integer.Sparse.merge (Integer.Sparse.scale (5760) (rows 185)) (Integer.Sparse.scale (-6336) (rows 186)) := by decide +kernel

theorem pairMergedZero180 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged180 x = 0 := by
  rw [pairMergeCheck180, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck181 : pairMerged181 = Integer.Sparse.merge pairMerged179 pairMerged180 := by decide +kernel

theorem pairMergedZero181 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged181 x = 0 := by
  rw [pairMergeCheck181, Integer.Sparse.eval_merge]
  rw [pairMergedZero179 x h, pairMergedZero180 x h]
  simp only [add_zero]

theorem pairMergeCheck182 : pairMerged182 = Integer.Sparse.merge (Integer.Sparse.scale (-12672) (rows 187)) (Integer.Sparse.scale (-13248) (rows 188)) := by decide +kernel

theorem pairMergedZero182 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged182 x = 0 := by
  rw [pairMergeCheck182, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck183 : pairMerged183 = Integer.Sparse.merge (Integer.Sparse.scale (6336) (rows 189)) (Integer.Sparse.scale (-5760) (rows 190)) := by decide +kernel

theorem pairMergedZero183 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged183 x = 0 := by
  rw [pairMergeCheck183, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck184 : pairMerged184 = Integer.Sparse.merge pairMerged182 pairMerged183 := by decide +kernel

theorem pairMergedZero184 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged184 x = 0 := by
  rw [pairMergeCheck184, Integer.Sparse.eval_merge]
  rw [pairMergedZero182 x h, pairMergedZero183 x h]
  simp only [add_zero]

theorem pairMergeCheck185 : pairMerged185 = Integer.Sparse.merge pairMerged181 pairMerged184 := by decide +kernel

theorem pairMergedZero185 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged185 x = 0 := by
  rw [pairMergeCheck185, Integer.Sparse.eval_merge]
  rw [pairMergedZero181 x h, pairMergedZero184 x h]
  simp only [add_zero]

theorem pairMergeCheck186 : pairMerged186 = Integer.Sparse.merge pairMerged178 pairMerged185 := by decide +kernel

theorem pairMergedZero186 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged186 x = 0 := by
  rw [pairMergeCheck186, Integer.Sparse.eval_merge]
  rw [pairMergedZero178 x h, pairMergedZero185 x h]
  simp only [add_zero]

theorem pairMergeCheck187 : pairMerged187 = Integer.Sparse.merge pairMerged171 pairMerged186 := by decide +kernel

theorem pairMergedZero187 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged187 x = 0 := by
  rw [pairMergeCheck187, Integer.Sparse.eval_merge]
  rw [pairMergedZero171 x h, pairMergedZero186 x h]
  simp only [add_zero]

theorem pairMergeCheck188 : pairMerged188 = Integer.Sparse.merge pairMerged156 pairMerged187 := by decide +kernel

theorem pairMergedZero188 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged188 x = 0 := by
  rw [pairMergeCheck188, Integer.Sparse.eval_merge]
  rw [pairMergedZero156 x h, pairMergedZero187 x h]
  simp only [add_zero]

theorem pairMergeCheck189 : pairMerged189 = Integer.Sparse.merge (Integer.Sparse.scale (25344) (rows 191)) (Integer.Sparse.scale (-28800) (rows 192)) := by decide +kernel

theorem pairMergedZero189 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged189 x = 0 := by
  rw [pairMergeCheck189, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck190 : pairMerged190 = Integer.Sparse.merge (Integer.Sparse.scale (6336) (rows 193)) (Integer.Sparse.scale (-20256) (rows 194)) := by decide +kernel

theorem pairMergedZero190 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged190 x = 0 := by
  rw [pairMergeCheck190, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck191 : pairMerged191 = Integer.Sparse.merge pairMerged189 pairMerged190 := by decide +kernel

theorem pairMergedZero191 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged191 x = 0 := by
  rw [pairMergeCheck191, Integer.Sparse.eval_merge]
  rw [pairMergedZero189 x h, pairMergedZero190 x h]
  simp only [add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck192 : pairMerged192 = Integer.Sparse.merge (Integer.Sparse.scale (4608) (rows 195)) (Integer.Sparse.scale (-21120) (rows 196)) := by decide +kernel

theorem pairMergedZero192 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged192 x = 0 := by
  rw [pairMergeCheck192, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck193 : pairMerged193 = Integer.Sparse.merge (Integer.Sparse.scale (74880) (rows 197)) (Integer.Sparse.scale (-27840) (rows 198)) := by decide +kernel

theorem pairMergedZero193 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged193 x = 0 := by
  rw [pairMergeCheck193, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck194 : pairMerged194 = Integer.Sparse.merge pairMerged192 pairMerged193 := by decide +kernel

theorem pairMergedZero194 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged194 x = 0 := by
  rw [pairMergeCheck194, Integer.Sparse.eval_merge]
  rw [pairMergedZero192 x h, pairMergedZero193 x h]
  simp only [add_zero]

theorem pairMergeCheck195 : pairMerged195 = Integer.Sparse.merge pairMerged191 pairMerged194 := by decide +kernel

theorem pairMergedZero195 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged195 x = 0 := by
  rw [pairMergeCheck195, Integer.Sparse.eval_merge]
  rw [pairMergedZero191 x h, pairMergedZero194 x h]
  simp only [add_zero]

theorem pairMergeCheck196 : pairMerged196 = Integer.Sparse.merge (Integer.Sparse.scale (-26784) (rows 199)) (Integer.Sparse.scale (-8480) (rows 200)) := by decide +kernel

theorem pairMergedZero196 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged196 x = 0 := by
  rw [pairMergeCheck196, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck197 : pairMerged197 = Integer.Sparse.merge (Integer.Sparse.scale (63840) (rows 201)) (Integer.Sparse.scale (1248) (rows 202)) := by decide +kernel

theorem pairMergedZero197 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged197 x = 0 := by
  rw [pairMergeCheck197, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck198 : pairMerged198 = Integer.Sparse.merge pairMerged196 pairMerged197 := by decide +kernel

theorem pairMergedZero198 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged198 x = 0 := by
  rw [pairMergeCheck198, Integer.Sparse.eval_merge]
  rw [pairMergedZero196 x h, pairMergedZero197 x h]
  simp only [add_zero]

theorem pairMergeCheck199 : pairMerged199 = Integer.Sparse.merge (Integer.Sparse.scale (266880) (rows 203)) (Integer.Sparse.scale (25536) (rows 204)) := by decide +kernel

theorem pairMergedZero199 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged199 x = 0 := by
  rw [pairMergeCheck199, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck200 : pairMerged200 = Integer.Sparse.merge (Integer.Sparse.scale (63360) (rows 205)) (Integer.Sparse.scale (7488) (rows 206)) := by decide +kernel

theorem pairMergedZero200 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged200 x = 0 := by
  rw [pairMergeCheck200, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck201 : pairMerged201 = Integer.Sparse.merge pairMerged199 pairMerged200 := by decide +kernel

theorem pairMergedZero201 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged201 x = 0 := by
  rw [pairMergeCheck201, Integer.Sparse.eval_merge]
  rw [pairMergedZero199 x h, pairMergedZero200 x h]
  simp only [add_zero]

theorem pairMergeCheck202 : pairMerged202 = Integer.Sparse.merge pairMerged198 pairMerged201 := by decide +kernel

theorem pairMergedZero202 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged202 x = 0 := by
  rw [pairMergeCheck202, Integer.Sparse.eval_merge]
  rw [pairMergedZero198 x h, pairMergedZero201 x h]
  simp only [add_zero]

theorem pairMergeCheck203 : pairMerged203 = Integer.Sparse.merge pairMerged195 pairMerged202 := by decide +kernel

theorem pairMergedZero203 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged203 x = 0 := by
  rw [pairMergeCheck203, Integer.Sparse.eval_merge]
  rw [pairMergedZero195 x h, pairMergedZero202 x h]
  simp only [add_zero]

theorem pairMergeCheck204 : pairMerged204 = Integer.Sparse.merge (Integer.Sparse.scale (-11520) (rows 207)) (Integer.Sparse.scale (22272) (rows 208)) := by decide +kernel

theorem pairMergedZero204 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged204 x = 0 := by
  rw [pairMergeCheck204, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck205 : pairMerged205 = Integer.Sparse.merge (Integer.Sparse.scale (-30144) (rows 209)) (Integer.Sparse.scale (-56592) (rows 210)) := by decide +kernel

theorem pairMergedZero205 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged205 x = 0 := by
  rw [pairMergeCheck205, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck206 : pairMerged206 = Integer.Sparse.merge pairMerged204 pairMerged205 := by decide +kernel

theorem pairMergedZero206 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged206 x = 0 := by
  rw [pairMergeCheck206, Integer.Sparse.eval_merge]
  rw [pairMergedZero204 x h, pairMergedZero205 x h]
  simp only [add_zero]

theorem pairMergeCheck207 : pairMerged207 = Integer.Sparse.merge (Integer.Sparse.scale (4608) (rows 211)) (Integer.Sparse.scale (-10752) (rows 212)) := by decide +kernel

theorem pairMergedZero207 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged207 x = 0 := by
  rw [pairMergeCheck207, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck208 : pairMerged208 = Integer.Sparse.merge (Integer.Sparse.scale (-13440) (rows 213)) (Integer.Sparse.scale (5760) (rows 214)) := by decide +kernel

theorem pairMergedZero208 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged208 x = 0 := by
  rw [pairMergeCheck208, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck209 : pairMerged209 = Integer.Sparse.merge pairMerged207 pairMerged208 := by decide +kernel

theorem pairMergedZero209 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged209 x = 0 := by
  rw [pairMergeCheck209, Integer.Sparse.eval_merge]
  rw [pairMergedZero207 x h, pairMergedZero208 x h]
  simp only [add_zero]

theorem pairMergeCheck210 : pairMerged210 = Integer.Sparse.merge pairMerged206 pairMerged209 := by decide +kernel

theorem pairMergedZero210 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged210 x = 0 := by
  rw [pairMergeCheck210, Integer.Sparse.eval_merge]
  rw [pairMergedZero206 x h, pairMergedZero209 x h]
  simp only [add_zero]

theorem pairMergeCheck211 : pairMerged211 = Integer.Sparse.merge (Integer.Sparse.scale (92640) (rows 215)) (Integer.Sparse.scale (26688) (rows 216)) := by decide +kernel

theorem pairMergedZero211 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged211 x = 0 := by
  rw [pairMergeCheck211, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck212 : pairMerged212 = Integer.Sparse.merge (Integer.Sparse.scale (-43200) (rows 217)) (Integer.Sparse.scale (8640) (rows 218)) := by decide +kernel

theorem pairMergedZero212 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged212 x = 0 := by
  rw [pairMergeCheck212, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck213 : pairMerged213 = Integer.Sparse.merge pairMerged211 pairMerged212 := by decide +kernel

theorem pairMergedZero213 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged213 x = 0 := by
  rw [pairMergeCheck213, Integer.Sparse.eval_merge]
  rw [pairMergedZero211 x h, pairMergedZero212 x h]
  simp only [add_zero]

theorem pairMergeCheck214 : pairMerged214 = Integer.Sparse.merge (Integer.Sparse.scale (208) (rows 219)) (Integer.Sparse.scale (-6912) (rows 220)) := by decide +kernel

theorem pairMergedZero214 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged214 x = 0 := by
  rw [pairMergeCheck214, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck215 : pairMerged215 = Integer.Sparse.merge (Integer.Sparse.scale (-12720) (rows 221)) (Integer.Sparse.scale (4608) (rows 222)) := by decide +kernel

theorem pairMergedZero215 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged215 x = 0 := by
  rw [pairMergeCheck215, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck216 : pairMerged216 = Integer.Sparse.merge pairMerged214 pairMerged215 := by decide +kernel

theorem pairMergedZero216 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged216 x = 0 := by
  rw [pairMergeCheck216, Integer.Sparse.eval_merge]
  rw [pairMergedZero214 x h, pairMergedZero215 x h]
  simp only [add_zero]

theorem pairMergeCheck217 : pairMerged217 = Integer.Sparse.merge pairMerged213 pairMerged216 := by decide +kernel

theorem pairMergedZero217 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged217 x = 0 := by
  rw [pairMergeCheck217, Integer.Sparse.eval_merge]
  rw [pairMergedZero213 x h, pairMergedZero216 x h]
  simp only [add_zero]

theorem pairMergeCheck218 : pairMerged218 = Integer.Sparse.merge pairMerged210 pairMerged217 := by decide +kernel

theorem pairMergedZero218 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged218 x = 0 := by
  rw [pairMergeCheck218, Integer.Sparse.eval_merge]
  rw [pairMergedZero210 x h, pairMergedZero217 x h]
  simp only [add_zero]

theorem pairMergeCheck219 : pairMerged219 = Integer.Sparse.merge pairMerged203 pairMerged218 := by decide +kernel

theorem pairMergedZero219 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged219 x = 0 := by
  rw [pairMergeCheck219, Integer.Sparse.eval_merge]
  rw [pairMergedZero203 x h, pairMergedZero218 x h]
  simp only [add_zero]

theorem pairMergeCheck220 : pairMerged220 = Integer.Sparse.merge (Integer.Sparse.scale (-19968) (rows 223)) (Integer.Sparse.scale (-3456) (rows 224)) := by decide +kernel

theorem pairMergedZero220 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged220 x = 0 := by
  rw [pairMergeCheck220, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck221 : pairMerged221 = Integer.Sparse.merge (Integer.Sparse.scale (78720) (rows 225)) (Integer.Sparse.scale (-11520) (rows 226)) := by decide +kernel

theorem pairMergedZero221 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged221 x = 0 := by
  rw [pairMergeCheck221, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck222 : pairMerged222 = Integer.Sparse.merge pairMerged220 pairMerged221 := by decide +kernel

theorem pairMergedZero222 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged222 x = 0 := by
  rw [pairMergeCheck222, Integer.Sparse.eval_merge]
  rw [pairMergedZero220 x h, pairMergedZero221 x h]
  simp only [add_zero]

theorem pairMergeCheck223 : pairMerged223 = Integer.Sparse.merge (Integer.Sparse.scale (-14272) (rows 227)) (Integer.Sparse.scale (7200) (rows 228)) := by decide +kernel

theorem pairMergedZero223 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged223 x = 0 := by
  rw [pairMergeCheck223, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Block7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergeCheck224 : pairMerged224 = Integer.Sparse.merge (Integer.Sparse.scale (8640) (rows 229)) (Integer.Sparse.scale (-77280) (rows 230)) := by decide +kernel

theorem pairMergedZero224 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged224 x = 0 := by
  rw [pairMergeCheck224, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck225 : pairMerged225 = Integer.Sparse.merge pairMerged223 pairMerged224 := by decide +kernel

theorem pairMergedZero225 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged225 x = 0 := by
  rw [pairMergeCheck225, Integer.Sparse.eval_merge]
  rw [pairMergedZero223 x h, pairMergedZero224 x h]
  simp only [add_zero]

theorem pairMergeCheck226 : pairMerged226 = Integer.Sparse.merge pairMerged222 pairMerged225 := by decide +kernel

theorem pairMergedZero226 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged226 x = 0 := by
  rw [pairMergeCheck226, Integer.Sparse.eval_merge]
  rw [pairMergedZero222 x h, pairMergedZero225 x h]
  simp only [add_zero]

theorem pairMergeCheck227 : pairMerged227 = Integer.Sparse.merge (Integer.Sparse.scale (31680) (rows 231)) (Integer.Sparse.scale (-11520) (rows 232)) := by decide +kernel

theorem pairMergedZero227 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged227 x = 0 := by
  rw [pairMergeCheck227, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck228 : pairMerged228 = Integer.Sparse.merge (Integer.Sparse.scale (-34176) (rows 233)) (Integer.Sparse.scale (25536) (rows 234)) := by decide +kernel

theorem pairMergedZero228 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged228 x = 0 := by
  rw [pairMergeCheck228, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck229 : pairMerged229 = Integer.Sparse.merge pairMerged227 pairMerged228 := by decide +kernel

theorem pairMergedZero229 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged229 x = 0 := by
  rw [pairMergeCheck229, Integer.Sparse.eval_merge]
  rw [pairMergedZero227 x h, pairMergedZero228 x h]
  simp only [add_zero]

theorem pairMergeCheck230 : pairMerged230 = Integer.Sparse.merge (Integer.Sparse.scale (2880) (rows 235)) (Integer.Sparse.scale (-255360) (rows 236)) := by decide +kernel

theorem pairMergedZero230 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged230 x = 0 := by
  rw [pairMergeCheck230, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck231 : pairMerged231 = Integer.Sparse.merge (Integer.Sparse.scale (-224640) (rows 237)) (Integer.Sparse.scale (1728) (rows 238)) := by decide +kernel

theorem pairMergedZero231 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged231 x = 0 := by
  rw [pairMergeCheck231, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck232 : pairMerged232 = Integer.Sparse.merge pairMerged230 pairMerged231 := by decide +kernel

theorem pairMergedZero232 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged232 x = 0 := by
  rw [pairMergeCheck232, Integer.Sparse.eval_merge]
  rw [pairMergedZero230 x h, pairMergedZero231 x h]
  simp only [add_zero]

theorem pairMergeCheck233 : pairMerged233 = Integer.Sparse.merge pairMerged229 pairMerged232 := by decide +kernel

theorem pairMergedZero233 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged233 x = 0 := by
  rw [pairMergeCheck233, Integer.Sparse.eval_merge]
  rw [pairMergedZero229 x h, pairMergedZero232 x h]
  simp only [add_zero]

theorem pairMergeCheck234 : pairMerged234 = Integer.Sparse.merge pairMerged226 pairMerged233 := by decide +kernel

theorem pairMergedZero234 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged234 x = 0 := by
  rw [pairMergeCheck234, Integer.Sparse.eval_merge]
  rw [pairMergedZero226 x h, pairMergedZero233 x h]
  simp only [add_zero]

theorem pairMergeCheck235 : pairMerged235 = Integer.Sparse.merge (Integer.Sparse.scale (-14400) (rows 239)) (Integer.Sparse.scale (-57600) (rows 240)) := by decide +kernel

theorem pairMergedZero235 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged235 x = 0 := by
  rw [pairMergeCheck235, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck236 : pairMerged236 = Integer.Sparse.merge (Integer.Sparse.scale (4896) (rows 241)) (Integer.Sparse.scale (-2016) (rows 242)) := by decide +kernel

theorem pairMergedZero236 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged236 x = 0 := by
  rw [pairMergeCheck236, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck237 : pairMerged237 = Integer.Sparse.merge pairMerged235 pairMerged236 := by decide +kernel

theorem pairMergedZero237 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged237 x = 0 := by
  rw [pairMergeCheck237, Integer.Sparse.eval_merge]
  rw [pairMergedZero235 x h, pairMergedZero236 x h]
  simp only [add_zero]

theorem pairMergeCheck238 : pairMerged238 = Integer.Sparse.merge (Integer.Sparse.scale (4608) (rows 243)) (Integer.Sparse.scale (-4896) (rows 244)) := by decide +kernel

theorem pairMergedZero238 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged238 x = 0 := by
  rw [pairMergeCheck238, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck239 : pairMerged239 = Integer.Sparse.merge (Integer.Sparse.scale (-1728) (rows 245)) (Integer.Sparse.scale (-40320) (rows 246)) := by decide +kernel

theorem pairMergedZero239 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged239 x = 0 := by
  rw [pairMergeCheck239, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck240 : pairMerged240 = Integer.Sparse.merge pairMerged238 pairMerged239 := by decide +kernel

theorem pairMergedZero240 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged240 x = 0 := by
  rw [pairMergeCheck240, Integer.Sparse.eval_merge]
  rw [pairMergedZero238 x h, pairMergedZero239 x h]
  simp only [add_zero]

theorem pairMergeCheck241 : pairMerged241 = Integer.Sparse.merge pairMerged237 pairMerged240 := by decide +kernel

theorem pairMergedZero241 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged241 x = 0 := by
  rw [pairMergeCheck241, Integer.Sparse.eval_merge]
  rw [pairMergedZero237 x h, pairMergedZero240 x h]
  simp only [add_zero]

theorem pairMergeCheck242 : pairMerged242 = Integer.Sparse.merge (Integer.Sparse.scale (12672) (rows 247)) (Integer.Sparse.scale (17280) (rows 248)) := by decide +kernel

theorem pairMergedZero242 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged242 x = 0 := by
  rw [pairMergeCheck242, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck243 : pairMerged243 = Integer.Sparse.merge (Integer.Sparse.scale (-11520) (rows 249)) (Integer.Sparse.scale (-4608) (rows 250)) := by decide +kernel

theorem pairMergedZero243 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged243 x = 0 := by
  rw [pairMergeCheck243, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck244 : pairMerged244 = Integer.Sparse.merge pairMerged242 pairMerged243 := by decide +kernel

theorem pairMergedZero244 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged244 x = 0 := by
  rw [pairMergeCheck244, Integer.Sparse.eval_merge]
  rw [pairMergedZero242 x h, pairMergedZero243 x h]
  simp only [add_zero]

theorem pairMergeCheck245 : pairMerged245 = Integer.Sparse.merge (Integer.Sparse.scale (11520) (rows 251)) (Integer.Sparse.scale (-12672) (rows 252)) := by decide +kernel

theorem pairMergedZero245 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged245 x = 0 := by
  rw [pairMergeCheck245, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck246 : pairMerged246 = Integer.Sparse.merge (Integer.Sparse.scale (28800) (rows 253)) (Integer.Sparse.scale (11520) (rows 254)) := by decide +kernel

theorem pairMergedZero246 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged246 x = 0 := by
  rw [pairMergeCheck246, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem pairMergeCheck247 : pairMerged247 = Integer.Sparse.merge pairMerged245 pairMerged246 := by decide +kernel

theorem pairMergedZero247 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged247 x = 0 := by
  rw [pairMergeCheck247, Integer.Sparse.eval_merge]
  rw [pairMergedZero245 x h, pairMergedZero246 x h]
  simp only [add_zero]

theorem pairMergeCheck248 : pairMerged248 = Integer.Sparse.merge pairMerged244 pairMerged247 := by decide +kernel

theorem pairMergedZero248 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged248 x = 0 := by
  rw [pairMergeCheck248, Integer.Sparse.eval_merge]
  rw [pairMergedZero244 x h, pairMergedZero247 x h]
  simp only [add_zero]

theorem pairMergeCheck249 : pairMerged249 = Integer.Sparse.merge pairMerged241 pairMerged248 := by decide +kernel

theorem pairMergedZero249 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged249 x = 0 := by
  rw [pairMergeCheck249, Integer.Sparse.eval_merge]
  rw [pairMergedZero241 x h, pairMergedZero248 x h]
  simp only [add_zero]

theorem pairMergeCheck250 : pairMerged250 = Integer.Sparse.merge pairMerged234 pairMerged249 := by decide +kernel

theorem pairMergedZero250 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged250 x = 0 := by
  rw [pairMergeCheck250, Integer.Sparse.eval_merge]
  rw [pairMergedZero234 x h, pairMergedZero249 x h]
  simp only [add_zero]

theorem pairMergeCheck251 : pairMerged251 = Integer.Sparse.merge pairMerged219 pairMerged250 := by decide +kernel

theorem pairMergedZero251 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged251 x = 0 := by
  rw [pairMergeCheck251, Integer.Sparse.eval_merge]
  rw [pairMergedZero219 x h, pairMergedZero250 x h]
  simp only [add_zero]

theorem pairMergeCheck252 : pairMerged252 = Integer.Sparse.merge pairMerged188 pairMerged251 := by decide +kernel

theorem pairMergedZero252 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged252 x = 0 := by
  rw [pairMergeCheck252, Integer.Sparse.eval_merge]
  rw [pairMergedZero188 x h, pairMergedZero251 x h]
  simp only [add_zero]

theorem pairMergeCheck253 : pairMerged253 = Integer.Sparse.merge pairMerged125 pairMerged252 := by decide +kernel

theorem pairMergedZero253 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged253 x = 0 := by
  rw [pairMergeCheck253, Integer.Sparse.eval_merge]
  rw [pairMergedZero125 x h, pairMergedZero252 x h]
  simp only [add_zero]

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairMerge_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairData

theorem pairTargetPermutation0 : List.Perm target0 pairMerged253 := by decide +kernel

theorem mergeConsequence0 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval target0 x = 0 := by
  rw [Integer.Sparse.eval_perm pairTargetPermutation0]
  exact pairMergedZero253 x h

end MUB6.Certificate.PairData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSources_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem targetZero0_e_oai {H : CMatrix} (hH : IsHadamard H) :
    Integer.Sparse.eval PairData.target0 (momentVector H) = 0 :=
  PairData.mergeConsequence0 _ (allRowsSound_e hH)

end MUB6.Certificate.PairSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e_oai := @OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e_oai
