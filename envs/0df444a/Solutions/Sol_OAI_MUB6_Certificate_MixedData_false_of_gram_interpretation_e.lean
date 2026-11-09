-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:48:21.028198+00:00
-- url     : https://prove2.me/submissions/683b7e05-fa18-4021-9c54-9ad0a92e5392
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E180
import Definitions.Def_OAIQ106E059
import Definitions.Def_OAIQ106E183
import Definitions.Def_OAIQ106E185
import Definitions.Def_OAIQ106E186
import Definitions.Def_OAIQ106E069
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E078
import Theorems.Thm_OAI_MUB6_Certificate_GramNonnegative_sourceGram_nonneg_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedEval2452_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1210_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1511_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1814_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero2421_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Integer
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer coefficient checking after denominator clearing. The arithmetic
checker uses only integer operations; its interpretation remains over arbitrary
real moment vectors. -/
namespace MUB6.Certificate.Integer

open scoped BigOperators

namespace Sparse

variable {ι : Type*}

theorem eval_le_abs_sum (v : Sparse ι) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    eval v x ≤ (v.map fun p => |(p.2 : ℝ)|).sum := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, List.map_cons, List.sum_cons]
    apply add_le_add _ ih
    calc
      (p.2 : ℝ) * x p.1 ≤ |(p.2 : ℝ) * x p.1| := le_abs_self _
      _ = |(p.2 : ℝ)| * |x p.1| := abs_mul _ _
      _ ≤ |(p.2 : ℝ)| * 1 := mul_le_mul_of_nonneg_left (hx p.1) (abs_nonneg _)
      _ = |(p.2 : ℝ)| := mul_one _

end Sparse

end MUB6.Certificate.Integer

end OAI
end

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedData_Expression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem denominator_pos : 0 < denominator := by decide

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_MixedResidual
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_append _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_merge _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem residualBound0 (x : Fin 3237 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1) :
    Integer.Sparse.eval targetRow23 x ≤ -3431846511326182440960 := by
  have h := Integer.Sparse.eval_le_abs_sum residualTail x hx
  have ha : (residualTail.map (fun p => |(p.2 : ℝ)|)).sum = 129038594601492817920 := by
    norm_num [residualTail, targetRow23]
  rw [ha] at h
  have heq : targetRow23 = (0, (-3560885105927675258880 : ℤ)) :: residualTail := rfl
  rw [heq, Integer.Sparse.eval_cons, hzero]
  norm_num only [Int.cast_neg, Int.cast_ofNat, mul_one]
  linarith

theorem residualBound1 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow24 x ≤ 57809244737470464000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow24 x hx
  have ha : (targetRow24.map (fun p => |(p.2 : ℝ)|)).sum = 57809244737470464000 := by
    norm_num [targetRow24]
  rw [ha] at h
  exact h

theorem residualBound2 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow25 x ≤ 208460565551960064000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow25 x hx
  have ha : (targetRow25.map (fun p => |(p.2 : ℝ)|)).sum = 208460565551960064000 := by
    norm_num [targetRow25]
  rw [ha] at h
  exact h

theorem residualBound3 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow26 x ≤ 342451535685706137600 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow26 x hx
  have ha : (targetRow26.map (fun p => |(p.2 : ℝ)|)).sum = 342451535685706137600 := by
    norm_num [targetRow26]
  rw [ha] at h
  exact h

theorem residualBound4 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow27 x ≤ 57870913835040768000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow27 x hx
  have ha : (targetRow27.map (fun p => |(p.2 : ℝ)|)).sum = 57870913835040768000 := by
    norm_num [targetRow27]
  rw [ha] at h
  exact h

theorem residualBound5 (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    Integer.Sparse.eval targetRow28 x ≤ 247845907767951360000 := by
  have h := Integer.Sparse.eval_le_abs_sum targetRow28 x hx
  have ha : (targetRow28.map (fun p => |(p.2 : ℝ)|)).sum = 247845907767951360000 := by
    norm_num [targetRow28]
  rw [ha] at h
  exact h

theorem residualNegative (x : Fin 3237 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1) :
    Integer.Combination.eval targetRows x residualCombination < 0 := by
  have h0 := residualBound0 x hx hzero
  have h1 := residualBound1 x hx
  have h2 := residualBound2 x hx
  have h3 := residualBound3 x hx
  have h4 := residualBound4 x hx
  have h5 := residualBound5 x hx
  change (Integer.Sparse.eval targetRow23 x +
    (Integer.Sparse.eval targetRow24 x + Integer.Sparse.eval targetRow25 x)) +
    (Integer.Sparse.eval targetRow26 x +
    (Integer.Sparse.eval targetRow27 x + Integer.Sparse.eval targetRow28 x)) < 0
  linarith

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1211 : merged1211 = Integer.Sparse.merge (Integer.Sparse.scale (-34033899272019900019200) (sourceRows 1212)) (Integer.Sparse.scale (-34026631875017949081600) (sourceRows 1213)) := by decide +kernel

theorem mergedZero1211 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1211 x = 0 := by
  rw [mergeCheck1211, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1212 : merged1212 = Integer.Sparse.merge (Integer.Sparse.scale (72858026831405550336000) (sourceRows 1214)) (Integer.Sparse.scale (-34026631875017949081600) (sourceRows 1215)) := by decide +kernel

theorem mergedZero1212 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1212 x = 0 := by
  rw [mergeCheck1212, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1213 : merged1213 = Integer.Sparse.merge merged1211 merged1212 := by decide +kernel

theorem mergedZero1213 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1213 x = 0 := by
  rw [mergeCheck1213, Integer.Sparse.eval_merge]
  rw [mergedZero1211 x h, mergedZero1212 x h]
  simp only [add_zero]

theorem mergeCheck1214 : merged1214 = Integer.Sparse.merge (Integer.Sparse.scale (-34035055506110412230400) (sourceRows 1216)) (Integer.Sparse.scale (-265038594281810759692800) (sourceRows 1217)) := by decide +kernel

theorem mergedZero1214 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1214 x = 0 := by
  rw [mergeCheck1214, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1215 : merged1215 = Integer.Sparse.merge (Integer.Sparse.scale (125904545156737339574400) (sourceRows 1219)) (Integer.Sparse.scale (-262110469473264033619200) (sourceRows 1220)) := by decide +kernel

theorem mergedZero1215 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1215 x = 0 := by
  rw [mergeCheck1215, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1216 : merged1216 = Integer.Sparse.merge (Integer.Sparse.scale (320712423717507658502400) (sourceRows 1218)) merged1215 := by decide +kernel

theorem mergedZero1216 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1216 x = 0 := by
  rw [mergeCheck1216, Integer.Sparse.eval_merge]
  rw [mergedZero1215 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1217 : merged1217 = Integer.Sparse.merge merged1214 merged1216 := by decide +kernel

theorem mergedZero1217 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1217 x = 0 := by
  rw [mergeCheck1217, Integer.Sparse.eval_merge]
  rw [mergedZero1214 x h, mergedZero1216 x h]
  simp only [add_zero]

theorem mergeCheck1218 : merged1218 = Integer.Sparse.merge merged1213 merged1217 := by decide +kernel

theorem mergedZero1218 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1218 x = 0 := by
  rw [mergeCheck1218, Integer.Sparse.eval_merge]
  rw [mergedZero1213 x h, mergedZero1217 x h]
  simp only [add_zero]

theorem mergeCheck1219 : merged1219 = Integer.Sparse.merge (Integer.Sparse.scale (-136106527500071796326400) (sourceRows 1221)) (Integer.Sparse.scale (-353717234833168281600) (sourceRows 1222)) := by decide +kernel

theorem mergedZero1219 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1219 x = 0 := by
  rw [mergeCheck1219, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1220 : merged1220 = Integer.Sparse.merge (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1223)) (Integer.Sparse.scale (-160438488526973235398400) (sourceRows 1224)) := by decide +kernel

theorem mergedZero1220 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1220 x = 0 := by
  rw [mergeCheck1220, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1221 : merged1221 = Integer.Sparse.merge merged1219 merged1220 := by decide +kernel

theorem mergedZero1221 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1221 x = 0 := by
  rw [mergeCheck1221, Integer.Sparse.eval_merge]
  rw [mergedZero1219 x h, mergedZero1220 x h]
  simp only [add_zero]

theorem mergeCheck1222 : merged1222 = Integer.Sparse.merge (Integer.Sparse.scale (34026631875017949081600) (sourceRows 1225)) (Integer.Sparse.scale (160223846118616575993600) (sourceRows 1226)) := by decide +kernel

theorem mergedZero1222 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1222 x = 0 := by
  rw [mergeCheck1222, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1223 : merged1223 = Integer.Sparse.merge (Integer.Sparse.scale (-34026631875017949081600) (sourceRows 1228)) (Integer.Sparse.scale (-457217082732448650124800) (sourceRows 1229)) := by decide +kernel

theorem mergedZero1223 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1223 x = 0 := by
  rw [mergeCheck1223, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1224 : merged1224 = Integer.Sparse.merge (Integer.Sparse.scale (-34027238013247006617600) (sourceRows 1227)) merged1223 := by decide +kernel

theorem mergedZero1224 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1224 x = 0 := by
  rw [mergeCheck1224, Integer.Sparse.eval_merge]
  rw [mergedZero1223 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1225 : merged1225 = Integer.Sparse.merge merged1222 merged1224 := by decide +kernel

theorem mergedZero1225 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1225 x = 0 := by
  rw [mergeCheck1225, Integer.Sparse.eval_merge]
  rw [mergedZero1222 x h, mergedZero1224 x h]
  simp only [add_zero]

theorem mergeCheck1226 : merged1226 = Integer.Sparse.merge merged1221 merged1225 := by decide +kernel

theorem mergedZero1226 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1226 x = 0 := by
  rw [mergeCheck1226, Integer.Sparse.eval_merge]
  rw [mergedZero1221 x h, mergedZero1225 x h]
  simp only [add_zero]

theorem mergeCheck1227 : merged1227 = Integer.Sparse.merge merged1218 merged1226 := by decide +kernel

theorem mergedZero1227 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1227 x = 0 := by
  rw [mergeCheck1227, Integer.Sparse.eval_merge]
  rw [mergedZero1218 x h, mergedZero1226 x h]
  simp only [add_zero]

theorem mergeCheck1228 : merged1228 = Integer.Sparse.merge (Integer.Sparse.scale (-13988867782882732185600) (sourceRows 1230)) (Integer.Sparse.scale (-350565446568960000) (sourceRows 1231)) := by decide +kernel

theorem mergedZero1228 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1228 x = 0 := by
  rw [mergeCheck1228, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1229 : merged1229 = Integer.Sparse.merge (Integer.Sparse.scale (-85190927496192000) (sourceRows 1232)) (Integer.Sparse.scale (58427574428160000) (sourceRows 1233)) := by decide +kernel

theorem mergedZero1229 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1229 x = 0 := by
  rw [mergeCheck1229, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1230 : merged1230 = Integer.Sparse.merge merged1228 merged1229 := by decide +kernel

theorem mergedZero1230 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1230 x = 0 := by
  rw [mergeCheck1230, Integer.Sparse.eval_merge]
  rw [mergedZero1228 x h, mergedZero1229 x h]
  simp only [add_zero]

theorem mergeCheck1231 : merged1231 = Integer.Sparse.merge (Integer.Sparse.scale (-183884109554073600) (sourceRows 1234)) (Integer.Sparse.scale (5515531934320558080000) (sourceRows 1235)) := by decide +kernel

theorem mergedZero1231 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1231 x = 0 := by
  rw [mergeCheck1231, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1232 : merged1232 = Integer.Sparse.merge (Integer.Sparse.scale (-34016092116585291216000) (sourceRows 1237)) (Integer.Sparse.scale (34024466343935054131200) (sourceRows 1238)) := by decide +kernel

theorem mergedZero1232 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1232 x = 0 := by
  rw [mergeCheck1232, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1233 : merged1233 = Integer.Sparse.merge (Integer.Sparse.scale (-53502067681318248652800) (sourceRows 1236)) merged1232 := by decide +kernel

theorem mergedZero1233 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1233 x = 0 := by
  rw [mergeCheck1233, Integer.Sparse.eval_merge]
  rw [mergedZero1232 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1234 : merged1234 = Integer.Sparse.merge merged1231 merged1233 := by decide +kernel

theorem mergedZero1234 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1234 x = 0 := by
  rw [mergeCheck1234, Integer.Sparse.eval_merge]
  rw [mergedZero1231 x h, mergedZero1233 x h]
  simp only [add_zero]

theorem mergeCheck1235 : merged1235 = Integer.Sparse.merge merged1230 merged1234 := by decide +kernel

theorem mergedZero1235 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1235 x = 0 := by
  rw [mergeCheck1235, Integer.Sparse.eval_merge]
  rw [mergedZero1230 x h, mergedZero1234 x h]
  simp only [add_zero]

theorem mergeCheck1236 : merged1236 = Integer.Sparse.merge (Integer.Sparse.scale (-34022313745780747161600) (sourceRows 1239)) (Integer.Sparse.scale (-39456439605858923827200) (sourceRows 1240)) := by decide +kernel

theorem mergedZero1236 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1236 x = 0 := by
  rw [mergeCheck1236, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1237 : merged1237 = Integer.Sparse.merge (Integer.Sparse.scale (3773693393876448000) (sourceRows 1242)) (Integer.Sparse.scale (80260553754098458675200) (sourceRows 1243)) := by decide +kernel

theorem mergedZero1237 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1237 x = 0 := by
  rw [mergeCheck1237, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1238 : merged1238 = Integer.Sparse.merge (Integer.Sparse.scale (-158475001036065625497600) (sourceRows 1241)) merged1237 := by decide +kernel

theorem mergedZero1238 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1238 x = 0 := by
  rw [mergeCheck1238, Integer.Sparse.eval_merge]
  rw [mergedZero1237 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1239 : merged1239 = Integer.Sparse.merge merged1236 merged1238 := by decide +kernel

theorem mergedZero1239 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1239 x = 0 := by
  rw [mergeCheck1239, Integer.Sparse.eval_merge]
  rw [mergedZero1236 x h, mergedZero1238 x h]
  simp only [add_zero]

theorem mergeCheck1240 : merged1240 = Integer.Sparse.merge (Integer.Sparse.scale (-71237420881872719040000) (sourceRows 1244)) (Integer.Sparse.scale (-1770709794526310400) (sourceRows 1245)) := by decide +kernel

theorem mergedZero1240 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1240 x = 0 := by
  rw [mergeCheck1240, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1241 : merged1241 = Integer.Sparse.merge (Integer.Sparse.scale (3994536164775690240000) (sourceRows 1247)) (Integer.Sparse.scale (34093939529179779379200) (sourceRows 1248)) := by decide +kernel

theorem mergedZero1241 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1241 x = 0 := by
  rw [mergeCheck1241, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1242 : merged1242 = Integer.Sparse.merge (Integer.Sparse.scale (-52595575438776710860800) (sourceRows 1246)) merged1241 := by decide +kernel

theorem mergedZero1242 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1242 x = 0 := by
  rw [mergeCheck1242, Integer.Sparse.eval_merge]
  rw [mergedZero1241 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1243 : merged1243 = Integer.Sparse.merge merged1240 merged1242 := by decide +kernel

theorem mergedZero1243 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1243 x = 0 := by
  rw [mergeCheck1243, Integer.Sparse.eval_merge]
  rw [mergedZero1240 x h, mergedZero1242 x h]
  simp only [add_zero]

theorem mergeCheck1244 : merged1244 = Integer.Sparse.merge merged1239 merged1243 := by decide +kernel

theorem mergedZero1244 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1244 x = 0 := by
  rw [mergeCheck1244, Integer.Sparse.eval_merge]
  rw [mergedZero1239 x h, mergedZero1243 x h]
  simp only [add_zero]

theorem mergeCheck1245 : merged1245 = Integer.Sparse.merge merged1235 merged1244 := by decide +kernel

theorem mergedZero1245 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1245 x = 0 := by
  rw [mergeCheck1245, Integer.Sparse.eval_merge]
  rw [mergedZero1235 x h, mergedZero1244 x h]
  simp only [add_zero]

theorem mergeCheck1246 : merged1246 = Integer.Sparse.merge merged1227 merged1245 := by decide +kernel

theorem mergedZero1246 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1246 x = 0 := by
  rw [mergeCheck1246, Integer.Sparse.eval_merge]
  rw [mergedZero1227 x h, mergedZero1245 x h]
  simp only [add_zero]

theorem mergeCheck1247 : merged1247 = Integer.Sparse.merge (Integer.Sparse.scale (32432914213020888336000) (sourceRows 1249)) (Integer.Sparse.scale (-13392397926162259200) (sourceRows 1250)) := by decide +kernel

theorem mergedZero1247 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1247 x = 0 := by
  rw [mergeCheck1247, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1248 : merged1248 = Integer.Sparse.merge (Integer.Sparse.scale (-34024030514041956393600) (sourceRows 1251)) (Integer.Sparse.scale (-55217609241350692147200) (sourceRows 1252)) := by decide +kernel

theorem mergedZero1248 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1248 x = 0 := by
  rw [mergeCheck1248, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1249 : merged1249 = Integer.Sparse.merge merged1247 merged1248 := by decide +kernel

theorem mergedZero1249 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1249 x = 0 := by
  rw [mergeCheck1249, Integer.Sparse.eval_merge]
  rw [mergedZero1247 x h, mergedZero1248 x h]
  simp only [add_zero]

theorem mergeCheck1250 : merged1250 = Integer.Sparse.merge (Integer.Sparse.scale (-107344525693171531161600) (sourceRows 1253)) (Integer.Sparse.scale (68047982250221797286400) (sourceRows 1254)) := by decide +kernel

theorem mergedZero1250 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1250 x = 0 := by
  rw [mergeCheck1250, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1251 : merged1251 = Integer.Sparse.merge (Integer.Sparse.scale (-63451061495471481753600) (sourceRows 1256)) (Integer.Sparse.scale (-68048932687870108262400) (sourceRows 1257)) := by decide +kernel

theorem mergedZero1251 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1251 x = 0 := by
  rw [mergeCheck1251, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1252 : merged1252 = Integer.Sparse.merge (Integer.Sparse.scale (23283863861081544806400) (sourceRows 1255)) merged1251 := by decide +kernel

theorem mergedZero1252 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1252 x = 0 := by
  rw [mergeCheck1252, Integer.Sparse.eval_merge]
  rw [mergedZero1251 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1253 : merged1253 = Integer.Sparse.merge merged1250 merged1252 := by decide +kernel

theorem mergedZero1253 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1253 x = 0 := by
  rw [mergeCheck1253, Integer.Sparse.eval_merge]
  rw [mergedZero1250 x h, mergedZero1252 x h]
  simp only [add_zero]

theorem mergeCheck1254 : merged1254 = Integer.Sparse.merge merged1249 merged1253 := by decide +kernel

theorem mergedZero1254 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1254 x = 0 := by
  rw [mergeCheck1254, Integer.Sparse.eval_merge]
  rw [mergedZero1249 x h, mergedZero1253 x h]
  simp only [add_zero]

theorem mergeCheck1255 : merged1255 = Integer.Sparse.merge (Integer.Sparse.scale (34026161669945747366400) (sourceRows 1258)) (Integer.Sparse.scale (-23722859734505164800) (sourceRows 1259)) := by decide +kernel

theorem mergedZero1255 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1255 x = 0 := by
  rw [mergeCheck1255, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1256 : merged1256 = Integer.Sparse.merge (Integer.Sparse.scale (20716803233280000) (sourceRows 1261)) (Integer.Sparse.scale (863607620486761113600) (sourceRows 1262)) := by decide +kernel

theorem mergedZero1256 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1256 x = 0 := by
  rw [mergeCheck1256, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1257 : merged1257 = Integer.Sparse.merge (Integer.Sparse.scale (-6403435625374905600) (sourceRows 1260)) merged1256 := by decide +kernel

theorem mergedZero1257 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1257 x = 0 := by
  rw [mergeCheck1257, Integer.Sparse.eval_merge]
  rw [mergedZero1256 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1258 : merged1258 = Integer.Sparse.merge merged1255 merged1257 := by decide +kernel

theorem mergedZero1258 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1258 x = 0 := by
  rw [mergeCheck1258, Integer.Sparse.eval_merge]
  rw [mergedZero1255 x h, mergedZero1257 x h]
  simp only [add_zero]

theorem mergeCheck1259 : merged1259 = Integer.Sparse.merge (Integer.Sparse.scale (105279790694400) (sourceRows 1263)) (Integer.Sparse.scale (-122519538282222950400) (sourceRows 1264)) := by decide +kernel

theorem mergedZero1259 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1259 x = 0 := by
  rw [mergeCheck1259, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1260 : merged1260 = Integer.Sparse.merge (Integer.Sparse.scale (-3390093733017600) (sourceRows 1266)) (Integer.Sparse.scale (537227285385874728960) (sourceRows 1267)) := by decide +kernel

theorem mergedZero1260 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1260 x = 0 := by
  rw [mergeCheck1260, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1261 : merged1261 = Integer.Sparse.merge (Integer.Sparse.scale (-4166377012070380800) (sourceRows 1265)) merged1260 := by decide +kernel

theorem mergedZero1261 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1261 x = 0 := by
  rw [mergeCheck1261, Integer.Sparse.eval_merge]
  rw [mergedZero1260 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1262 : merged1262 = Integer.Sparse.merge merged1259 merged1261 := by decide +kernel

theorem mergedZero1262 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1262 x = 0 := by
  rw [mergeCheck1262, Integer.Sparse.eval_merge]
  rw [mergedZero1259 x h, mergedZero1261 x h]
  simp only [add_zero]

theorem mergeCheck1263 : merged1263 = Integer.Sparse.merge merged1258 merged1262 := by decide +kernel

theorem mergedZero1263 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1263 x = 0 := by
  rw [mergeCheck1263, Integer.Sparse.eval_merge]
  rw [mergedZero1258 x h, mergedZero1262 x h]
  simp only [add_zero]

theorem mergeCheck1264 : merged1264 = Integer.Sparse.merge merged1254 merged1263 := by decide +kernel

theorem mergedZero1264 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1264 x = 0 := by
  rw [mergeCheck1264, Integer.Sparse.eval_merge]
  rw [mergedZero1254 x h, mergedZero1263 x h]
  simp only [add_zero]

theorem mergeCheck1265 : merged1265 = Integer.Sparse.merge (Integer.Sparse.scale (-84741827788800) (sourceRows 1268)) (Integer.Sparse.scale (44773123396055040000) (sourceRows 1269)) := by decide +kernel

theorem mergedZero1265 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1265 x = 0 := by
  rw [mergeCheck1265, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1266 : merged1266 = Integer.Sparse.merge (Integer.Sparse.scale (-34028513712238877395200) (sourceRows 1270)) (Integer.Sparse.scale (-2633011454403477504000) (sourceRows 1271)) := by decide +kernel

theorem mergedZero1266 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1266 x = 0 := by
  rw [mergeCheck1266, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1267 : merged1267 = Integer.Sparse.merge merged1265 merged1266 := by decide +kernel

theorem mergedZero1267 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1267 x = 0 := by
  rw [mergeCheck1267, Integer.Sparse.eval_merge]
  rw [mergedZero1265 x h, mergedZero1266 x h]
  simp only [add_zero]

theorem mergeCheck1268 : merged1268 = Integer.Sparse.merge (Integer.Sparse.scale (9853597515934448640) (sourceRows 1272)) (Integer.Sparse.scale (-2633251810224817152000) (sourceRows 1273)) := by decide +kernel

theorem mergedZero1268 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1268 x = 0 := by
  rw [mergeCheck1268, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1269 : merged1269 = Integer.Sparse.merge (Integer.Sparse.scale (-304352018926461067161600) (sourceRows 1275)) (Integer.Sparse.scale (397317042160237127577600) (sourceRows 1276)) := by decide +kernel

theorem mergedZero1269 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1269 x = 0 := by
  rw [mergeCheck1269, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1270 : merged1270 = Integer.Sparse.merge (Integer.Sparse.scale (59342241149764505856000) (sourceRows 1274)) merged1269 := by decide +kernel

theorem mergedZero1270 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1270 x = 0 := by
  rw [mergeCheck1270, Integer.Sparse.eval_merge]
  rw [mergedZero1269 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1271 : merged1271 = Integer.Sparse.merge merged1268 merged1270 := by decide +kernel

theorem mergedZero1271 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1271 x = 0 := by
  rw [mergeCheck1271, Integer.Sparse.eval_merge]
  rw [mergedZero1268 x h, mergedZero1270 x h]
  simp only [add_zero]

theorem mergeCheck1272 : merged1272 = Integer.Sparse.merge merged1267 merged1271 := by decide +kernel

theorem mergedZero1272 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1272 x = 0 := by
  rw [mergeCheck1272, Integer.Sparse.eval_merge]
  rw [mergedZero1267 x h, mergedZero1271 x h]
  simp only [add_zero]

theorem mergeCheck1273 : merged1273 = Integer.Sparse.merge (Integer.Sparse.scale (-111356643731003838720000) (sourceRows 1277)) (Integer.Sparse.scale (197201221056000) (sourceRows 1278)) := by decide +kernel

theorem mergedZero1273 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1273 x = 0 := by
  rw [mergeCheck1273, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1274 : merged1274 = Integer.Sparse.merge (Integer.Sparse.scale (16279279631997984000) (sourceRows 1280)) (Integer.Sparse.scale (-7695955372738348800) (sourceRows 1281)) := by decide +kernel

theorem mergedZero1274 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1274 x = 0 := by
  rw [mergeCheck1274, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1275 : merged1275 = Integer.Sparse.merge (Integer.Sparse.scale (380180507212800) (sourceRows 1279)) merged1274 := by decide +kernel

theorem mergedZero1275 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1275 x = 0 := by
  rw [mergeCheck1275, Integer.Sparse.eval_merge]
  rw [mergedZero1274 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1276 : merged1276 = Integer.Sparse.merge merged1273 merged1275 := by decide +kernel

theorem mergedZero1276 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1276 x = 0 := by
  rw [mergeCheck1276, Integer.Sparse.eval_merge]
  rw [mergedZero1273 x h, mergedZero1275 x h]
  simp only [add_zero]

theorem mergeCheck1277 : merged1277 = Integer.Sparse.merge (Integer.Sparse.scale (-139662475610112000) (sourceRows 1282)) (Integer.Sparse.scale (9211968083624140800) (sourceRows 1283)) := by decide +kernel

theorem mergedZero1277 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1277 x = 0 := by
  rw [mergeCheck1277, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1278 : merged1278 = Integer.Sparse.merge (Integer.Sparse.scale (-279324951220224000) (sourceRows 1285)) (Integer.Sparse.scale (5497875886642070400) (sourceRows 1286)) := by decide +kernel

theorem mergedZero1278 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1278 x = 0 := by
  rw [mergeCheck1278, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1279 : merged1279 = Integer.Sparse.merge (Integer.Sparse.scale (-13260950362186329600) (sourceRows 1284)) merged1278 := by decide +kernel

theorem mergedZero1279 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1279 x = 0 := by
  rw [mergeCheck1279, Integer.Sparse.eval_merge]
  rw [mergedZero1278 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1280 : merged1280 = Integer.Sparse.merge merged1277 merged1279 := by decide +kernel

theorem mergedZero1280 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1280 x = 0 := by
  rw [mergeCheck1280, Integer.Sparse.eval_merge]
  rw [mergedZero1277 x h, mergedZero1279 x h]
  simp only [add_zero]

theorem mergeCheck1281 : merged1281 = Integer.Sparse.merge merged1276 merged1280 := by decide +kernel

theorem mergedZero1281 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1281 x = 0 := by
  rw [mergeCheck1281, Integer.Sparse.eval_merge]
  rw [mergedZero1276 x h, mergedZero1280 x h]
  simp only [add_zero]

theorem mergeCheck1282 : merged1282 = Integer.Sparse.merge merged1272 merged1281 := by decide +kernel

theorem mergedZero1282 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1282 x = 0 := by
  rw [mergeCheck1282, Integer.Sparse.eval_merge]
  rw [mergedZero1272 x h, mergedZero1281 x h]
  simp only [add_zero]

theorem mergeCheck1283 : merged1283 = Integer.Sparse.merge merged1264 merged1282 := by decide +kernel

theorem mergedZero1283 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1283 x = 0 := by
  rw [mergeCheck1283, Integer.Sparse.eval_merge]
  rw [mergedZero1264 x h, mergedZero1282 x h]
  simp only [add_zero]

theorem mergeCheck1284 : merged1284 = Integer.Sparse.merge merged1246 merged1283 := by decide +kernel

theorem mergedZero1284 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1284 x = 0 := by
  rw [mergeCheck1284, Integer.Sparse.eval_merge]
  rw [mergedZero1246 x h, mergedZero1283 x h]
  simp only [add_zero]

theorem mergeCheck1285 : merged1285 = Integer.Sparse.merge (Integer.Sparse.scale (10685896224092409600) (sourceRows 1287)) (Integer.Sparse.scale (92486332745480575843200) (sourceRows 1288)) := by decide +kernel

theorem mergedZero1285 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1285 x = 0 := by
  rw [mergeCheck1285, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1286 : merged1286 = Integer.Sparse.merge (Integer.Sparse.scale (-92454955877506014374400) (sourceRows 1289)) (Integer.Sparse.scale (-138706929839442996259200) (sourceRows 1290)) := by decide +kernel

theorem mergedZero1286 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1286 x = 0 := by
  rw [mergeCheck1286, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1287 : merged1287 = Integer.Sparse.merge merged1285 merged1286 := by decide +kernel

theorem mergedZero1287 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1287 x = 0 := by
  rw [mergeCheck1287, Integer.Sparse.eval_merge]
  rw [mergedZero1285 x h, mergedZero1286 x h]
  simp only [add_zero]

theorem mergeCheck1288 : merged1288 = Integer.Sparse.merge (Integer.Sparse.scale (92450485839656036131200) (sourceRows 1291)) (Integer.Sparse.scale (71625783399032217600) (sourceRows 1292)) := by decide +kernel

theorem mergedZero1288 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1288 x = 0 := by
  rw [mergeCheck1288, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1289 : merged1289 = Integer.Sparse.merge (Integer.Sparse.scale (5857675691446555200) (sourceRows 1294)) (Integer.Sparse.scale (-1801997365742364672000) (sourceRows 1295)) := by decide +kernel

theorem mergedZero1289 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1289 x = 0 := by
  rw [mergeCheck1289, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1290 : merged1290 = Integer.Sparse.merge (Integer.Sparse.scale (-1802027858388516864000) (sourceRows 1293)) merged1289 := by decide +kernel

theorem mergedZero1290 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1290 x = 0 := by
  rw [mergeCheck1290, Integer.Sparse.eval_merge]
  rw [mergedZero1289 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1291 : merged1291 = Integer.Sparse.merge merged1288 merged1290 := by decide +kernel

theorem mergedZero1291 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1291 x = 0 := by
  rw [mergeCheck1291, Integer.Sparse.eval_merge]
  rw [mergedZero1288 x h, mergedZero1290 x h]
  simp only [add_zero]

theorem mergeCheck1292 : merged1292 = Integer.Sparse.merge merged1287 merged1291 := by decide +kernel

theorem mergedZero1292 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1292 x = 0 := by
  rw [mergeCheck1292, Integer.Sparse.eval_merge]
  rw [mergedZero1287 x h, mergedZero1291 x h]
  simp only [add_zero]

theorem mergeCheck1293 : merged1293 = Integer.Sparse.merge (Integer.Sparse.scale (-3091156623025996492800) (sourceRows 1296)) (Integer.Sparse.scale (-49918890338321666457600) (sourceRows 1297)) := by decide +kernel

theorem mergedZero1293 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1293 x = 0 := by
  rw [mergeCheck1293, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1294 : merged1294 = Integer.Sparse.merge (Integer.Sparse.scale (-20480293768265888256000) (sourceRows 1299)) (Integer.Sparse.scale (324597635712000) (sourceRows 1300)) := by decide +kernel

theorem mergedZero1294 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1294 x = 0 := by
  rw [mergeCheck1294, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1295 : merged1295 = Integer.Sparse.merge (Integer.Sparse.scale (21717428008237671628800) (sourceRows 1298)) merged1294 := by decide +kernel

theorem mergedZero1295 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1295 x = 0 := by
  rw [mergeCheck1295, Integer.Sparse.eval_merge]
  rw [mergedZero1294 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1296 : merged1296 = Integer.Sparse.merge merged1293 merged1295 := by decide +kernel

theorem mergedZero1296 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1296 x = 0 := by
  rw [mergeCheck1296, Integer.Sparse.eval_merge]
  rw [mergedZero1293 x h, mergedZero1295 x h]
  simp only [add_zero]

theorem mergeCheck1297 : merged1297 = Integer.Sparse.merge (Integer.Sparse.scale (31506140625016619520) (sourceRows 1301)) (Integer.Sparse.scale (6445640557202079744000) (sourceRows 1302)) := by decide +kernel

theorem mergedZero1297 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1297 x = 0 := by
  rw [mergeCheck1297, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1298 : merged1298 = Integer.Sparse.merge (Integer.Sparse.scale (6445975225069771776000) (sourceRows 1304)) (Integer.Sparse.scale (-6781320735995944857600) (sourceRows 1305)) := by decide +kernel

theorem mergedZero1298 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1298 x = 0 := by
  rw [mergeCheck1298, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1299 : merged1299 = Integer.Sparse.merge (Integer.Sparse.scale (247038793002543144960) (sourceRows 1303)) merged1298 := by decide +kernel

theorem mergedZero1299 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1299 x = 0 := by
  rw [mergeCheck1299, Integer.Sparse.eval_merge]
  rw [mergedZero1298 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1300 : merged1300 = Integer.Sparse.merge merged1297 merged1299 := by decide +kernel

theorem mergedZero1300 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1300 x = 0 := by
  rw [mergeCheck1300, Integer.Sparse.eval_merge]
  rw [mergedZero1297 x h, mergedZero1299 x h]
  simp only [add_zero]

theorem mergeCheck1301 : merged1301 = Integer.Sparse.merge merged1296 merged1300 := by decide +kernel

theorem mergedZero1301 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1301 x = 0 := by
  rw [mergeCheck1301, Integer.Sparse.eval_merge]
  rw [mergedZero1296 x h, mergedZero1300 x h]
  simp only [add_zero]

theorem mergeCheck1302 : merged1302 = Integer.Sparse.merge merged1292 merged1301 := by decide +kernel

theorem mergedZero1302 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1302 x = 0 := by
  rw [mergeCheck1302, Integer.Sparse.eval_merge]
  rw [mergedZero1292 x h, mergedZero1301 x h]
  simp only [add_zero]

theorem mergeCheck1303 : merged1303 = Integer.Sparse.merge (Integer.Sparse.scale (-94072220875222332825600) (sourceRows 1306)) (Integer.Sparse.scale (-35145952387923518668800) (sourceRows 1307)) := by decide +kernel

theorem mergedZero1303 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1303 x = 0 := by
  rw [mergeCheck1303, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1304 : merged1304 = Integer.Sparse.merge (Integer.Sparse.scale (83164743506435022028800) (sourceRows 1308)) (Integer.Sparse.scale (324597635712000) (sourceRows 1309)) := by decide +kernel

theorem mergedZero1304 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1304 x = 0 := by
  rw [mergeCheck1304, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1305 : merged1305 = Integer.Sparse.merge merged1303 merged1304 := by decide +kernel

theorem mergedZero1305 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1305 x = 0 := by
  rw [mergeCheck1305, Integer.Sparse.eval_merge]
  rw [mergedZero1303 x h, mergedZero1304 x h]
  simp only [add_zero]

theorem mergeCheck1306 : merged1306 = Integer.Sparse.merge (Integer.Sparse.scale (173187470131200) (sourceRows 1310)) (Integer.Sparse.scale (198742970700610560) (sourceRows 1311)) := by decide +kernel

theorem mergedZero1306 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1306 x = 0 := by
  rw [mergeCheck1306, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1307 : merged1307 = Integer.Sparse.merge (Integer.Sparse.scale (-21681282096458611200) (sourceRows 1313)) (Integer.Sparse.scale (1786554994142822400) (sourceRows 1314)) := by decide +kernel

theorem mergedZero1307 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1307 x = 0 := by
  rw [mergeCheck1307, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1308 : merged1308 = Integer.Sparse.merge (Integer.Sparse.scale (131259251935393505280) (sourceRows 1312)) merged1307 := by decide +kernel

theorem mergedZero1308 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1308 x = 0 := by
  rw [mergeCheck1308, Integer.Sparse.eval_merge]
  rw [mergedZero1307 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1309 : merged1309 = Integer.Sparse.merge merged1306 merged1308 := by decide +kernel

theorem mergedZero1309 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1309 x = 0 := by
  rw [mergeCheck1309, Integer.Sparse.eval_merge]
  rw [mergedZero1306 x h, mergedZero1308 x h]
  simp only [add_zero]

theorem mergeCheck1310 : merged1310 = Integer.Sparse.merge merged1305 merged1309 := by decide +kernel

theorem mergedZero1310 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1310 x = 0 := by
  rw [mergeCheck1310, Integer.Sparse.eval_merge]
  rw [mergedZero1305 x h, mergedZero1309 x h]
  simp only [add_zero]

theorem mergeCheck1311 : merged1311 = Integer.Sparse.merge (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1315)) (Integer.Sparse.scale (68053263750035898163200) (sourceRows 1316)) := by decide +kernel

theorem mergedZero1311 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1311 x = 0 := by
  rw [mergeCheck1311, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1312 : merged1312 = Integer.Sparse.merge (Integer.Sparse.scale (-4389693635021083200) (sourceRows 1318)) (Integer.Sparse.scale (161496031378784256000) (sourceRows 1319)) := by decide +kernel

theorem mergedZero1312 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1312 x = 0 := by
  rw [mergeCheck1312, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1313 : merged1313 = Integer.Sparse.merge (Integer.Sparse.scale (161522266954825728000) (sourceRows 1317)) merged1312 := by decide +kernel

theorem mergedZero1313 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1313 x = 0 := by
  rw [mergeCheck1313, Integer.Sparse.eval_merge]
  rw [mergedZero1312 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1314 : merged1314 = Integer.Sparse.merge merged1311 merged1313 := by decide +kernel

theorem mergedZero1314 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1314 x = 0 := by
  rw [mergeCheck1314, Integer.Sparse.eval_merge]
  rw [mergedZero1311 x h, mergedZero1313 x h]
  simp only [add_zero]

theorem mergeCheck1315 : merged1315 = Integer.Sparse.merge (Integer.Sparse.scale (1298435016403594137600) (sourceRows 1320)) (Integer.Sparse.scale (27973090770647578214400) (sourceRows 1321)) := by decide +kernel

theorem mergedZero1315 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1315 x = 0 := by
  rw [mergeCheck1315, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1316 : merged1316 = Integer.Sparse.merge (Integer.Sparse.scale (-121026056728111718400) (sourceRows 1323)) (Integer.Sparse.scale (1622988178560000) (sourceRows 1324)) := by decide +kernel

theorem mergedZero1316 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1316 x = 0 := by
  rw [mergeCheck1316, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1317 : merged1317 = Integer.Sparse.merge (Integer.Sparse.scale (27973909744183594598400) (sourceRows 1322)) merged1316 := by decide +kernel

theorem mergedZero1317 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1317 x = 0 := by
  rw [mergeCheck1317, Integer.Sparse.eval_merge]
  rw [mergedZero1316 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1318 : merged1318 = Integer.Sparse.merge merged1315 merged1317 := by decide +kernel

theorem mergedZero1318 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1318 x = 0 := by
  rw [mergeCheck1318, Integer.Sparse.eval_merge]
  rw [mergedZero1315 x h, mergedZero1317 x h]
  simp only [add_zero]

theorem mergeCheck1319 : merged1319 = Integer.Sparse.merge merged1314 merged1318 := by decide +kernel

theorem mergedZero1319 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1319 x = 0 := by
  rw [mergeCheck1319, Integer.Sparse.eval_merge]
  rw [mergedZero1314 x h, mergedZero1318 x h]
  simp only [add_zero]

theorem mergeCheck1320 : merged1320 = Integer.Sparse.merge merged1310 merged1319 := by decide +kernel

theorem mergedZero1320 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1320 x = 0 := by
  rw [mergeCheck1320, Integer.Sparse.eval_merge]
  rw [mergedZero1310 x h, mergedZero1319 x h]
  simp only [add_zero]

theorem mergeCheck1321 : merged1321 = Integer.Sparse.merge merged1302 merged1320 := by decide +kernel

theorem mergedZero1321 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1321 x = 0 := by
  rw [mergeCheck1321, Integer.Sparse.eval_merge]
  rw [mergedZero1302 x h, mergedZero1320 x h]
  simp only [add_zero]

theorem mergeCheck1322 : merged1322 = Integer.Sparse.merge (Integer.Sparse.scale (-19469873566957907016000) (sourceRows 1325)) (Integer.Sparse.scale (255572782488576000) (sourceRows 1326)) := by decide +kernel

theorem mergedZero1322 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1322 x = 0 := by
  rw [mergeCheck1322, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1323 : merged1323 = Integer.Sparse.merge (Integer.Sparse.scale (-139662475610112000) (sourceRows 1327)) (Integer.Sparse.scale (-34026631875017949081600) (sourceRows 1328)) := by decide +kernel

theorem mergedZero1323 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1323 x = 0 := by
  rw [mergeCheck1323, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1324 : merged1324 = Integer.Sparse.merge merged1322 merged1323 := by decide +kernel

theorem mergedZero1324 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1324 x = 0 := by
  rw [mergeCheck1324, Integer.Sparse.eval_merge]
  rw [mergedZero1322 x h, mergedZero1323 x h]
  simp only [add_zero]

theorem mergeCheck1325 : merged1325 = Integer.Sparse.merge (Integer.Sparse.scale (160007698931728196908800) (sourceRows 1329)) (Integer.Sparse.scale (-70299948854573929814400) (sourceRows 1330)) := by decide +kernel

theorem mergedZero1325 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1325 x = 0 := by
  rw [mergeCheck1325, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1326 : merged1326 = Integer.Sparse.merge (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1332)) (Integer.Sparse.scale (-33866598401389599753600) (sourceRows 1333)) := by decide +kernel

theorem mergedZero1326 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1326 x = 0 := by
  rw [mergeCheck1326, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1327 : merged1327 = Integer.Sparse.merge (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1331)) merged1326 := by decide +kernel

theorem mergedZero1327 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1327 x = 0 := by
  rw [mergeCheck1327, Integer.Sparse.eval_merge]
  rw [mergedZero1326 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1328 : merged1328 = Integer.Sparse.merge merged1325 merged1327 := by decide +kernel

theorem mergedZero1328 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1328 x = 0 := by
  rw [mergeCheck1328, Integer.Sparse.eval_merge]
  rw [mergedZero1325 x h, mergedZero1327 x h]
  simp only [add_zero]

theorem mergeCheck1329 : merged1329 = Integer.Sparse.merge merged1324 merged1328 := by decide +kernel

theorem mergedZero1329 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1329 x = 0 := by
  rw [mergeCheck1329, Integer.Sparse.eval_merge]
  rw [mergedZero1324 x h, mergedZero1328 x h]
  simp only [add_zero]

theorem mergeCheck1330 : merged1330 = Integer.Sparse.merge (Integer.Sparse.scale (641424847435015317004800) (sourceRows 1334)) (Integer.Sparse.scale (34026106026848095641600) (sourceRows 1335)) := by decide +kernel

theorem mergedZero1330 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1330 x = 0 := by
  rw [mergeCheck1330, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1331 : merged1331 = Integer.Sparse.merge (Integer.Sparse.scale (-126627381422519298451200) (sourceRows 1337)) (Integer.Sparse.scale (-34026631875017949081600) (sourceRows 1338)) := by decide +kernel

theorem mergedZero1331 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1331 x = 0 := by
  rw [mergeCheck1331, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1332 : merged1332 = Integer.Sparse.merge (Integer.Sparse.scale (34026631875017949081600) (sourceRows 1336)) merged1331 := by decide +kernel

theorem mergedZero1332 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1332 x = 0 := by
  rw [mergeCheck1332, Integer.Sparse.eval_merge]
  rw [mergedZero1331 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1333 : merged1333 = Integer.Sparse.merge merged1330 merged1332 := by decide +kernel

theorem mergedZero1333 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1333 x = 0 := by
  rw [mergeCheck1333, Integer.Sparse.eval_merge]
  rw [mergedZero1330 x h, mergedZero1332 x h]
  simp only [add_zero]

theorem mergeCheck1334 : merged1334 = Integer.Sparse.merge (Integer.Sparse.scale (19481269915626756249600) (sourceRows 1339)) (Integer.Sparse.scale (-350565446568960000) (sourceRows 1340)) := by decide +kernel

theorem mergedZero1334 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1334 x = 0 := by
  rw [mergeCheck1334, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1335 : merged1335 = Integer.Sparse.merge (Integer.Sparse.scale (-430965189607634841600) (sourceRows 1342)) (Integer.Sparse.scale (47105006164651774180800) (sourceRows 1343)) := by decide +kernel

theorem mergedZero1335 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1335 x = 0 := by
  rw [mergeCheck1335, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1336 : merged1336 = Integer.Sparse.merge (Integer.Sparse.scale (161016848378265600) (sourceRows 1341)) merged1335 := by decide +kernel

theorem mergedZero1336 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1336 x = 0 := by
  rw [mergeCheck1336, Integer.Sparse.eval_merge]
  rw [mergedZero1335 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1337 : merged1337 = Integer.Sparse.merge merged1334 merged1336 := by decide +kernel

theorem mergedZero1337 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1337 x = 0 := by
  rw [mergeCheck1337, Integer.Sparse.eval_merge]
  rw [mergedZero1334 x h, mergedZero1336 x h]
  simp only [add_zero]

theorem mergeCheck1338 : merged1338 = Integer.Sparse.merge merged1333 merged1337 := by decide +kernel

theorem mergedZero1338 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1338 x = 0 := by
  rw [mergeCheck1338, Integer.Sparse.eval_merge]
  rw [mergedZero1333 x h, mergedZero1337 x h]
  simp only [add_zero]

theorem mergeCheck1339 : merged1339 = Integer.Sparse.merge merged1329 merged1338 := by decide +kernel

theorem mergedZero1339 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1339 x = 0 := by
  rw [mergeCheck1339, Integer.Sparse.eval_merge]
  rw [mergedZero1329 x h, mergedZero1338 x h]
  simp only [add_zero]

theorem mergeCheck1340 : merged1340 = Integer.Sparse.merge (Integer.Sparse.scale (5598716419991136153600) (sourceRows 1344)) (Integer.Sparse.scale (122096895510444470784000) (sourceRows 1345)) := by decide +kernel

theorem mergedZero1340 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1340 x = 0 := by
  rw [mergeCheck1340, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1341 : merged1341 = Integer.Sparse.merge (Integer.Sparse.scale (-1293325381653671116800) (sourceRows 1346)) (Integer.Sparse.scale (313343307949237815513600) (sourceRows 1347)) := by decide +kernel

theorem mergedZero1341 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1341 x = 0 := by
  rw [mergeCheck1341, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1342 : merged1342 = Integer.Sparse.merge merged1340 merged1341 := by decide +kernel

theorem mergedZero1342 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1342 x = 0 := by
  rw [mergeCheck1342, Integer.Sparse.eval_merge]
  rw [mergedZero1340 x h, mergedZero1341 x h]
  simp only [add_zero]

theorem mergeCheck1343 : merged1343 = Integer.Sparse.merge (Integer.Sparse.scale (-67033139222730781900800) (sourceRows 1348)) (Integer.Sparse.scale (-43761173285259463219200) (sourceRows 1349)) := by decide +kernel

theorem mergedZero1343 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1343 x = 0 := by
  rw [mergeCheck1343, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1344 : merged1344 = Integer.Sparse.merge (Integer.Sparse.scale (-88276440281568773068800) (sourceRows 1351)) (Integer.Sparse.scale (431395002438401433600) (sourceRows 1352)) := by decide +kernel

theorem mergedZero1344 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1344 x = 0 := by
  rw [mergeCheck1344, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1345 : merged1345 = Integer.Sparse.merge (Integer.Sparse.scale (230241686838273008640000) (sourceRows 1350)) merged1344 := by decide +kernel

theorem mergedZero1345 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1345 x = 0 := by
  rw [mergeCheck1345, Integer.Sparse.eval_merge]
  rw [mergedZero1344 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1346 : merged1346 = Integer.Sparse.merge merged1343 merged1345 := by decide +kernel

theorem mergedZero1346 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1346 x = 0 := by
  rw [mergeCheck1346, Integer.Sparse.eval_merge]
  rw [mergedZero1343 x h, mergedZero1345 x h]
  simp only [add_zero]

theorem mergeCheck1347 : merged1347 = Integer.Sparse.merge merged1342 merged1346 := by decide +kernel

theorem mergedZero1347 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1347 x = 0 := by
  rw [mergeCheck1347, Integer.Sparse.eval_merge]
  rw [mergedZero1342 x h, mergedZero1346 x h]
  simp only [add_zero]

theorem mergeCheck1348 : merged1348 = Integer.Sparse.merge (Integer.Sparse.scale (-34500329276314053600000) (sourceRows 1353)) (Integer.Sparse.scale (-209651430124612013126400) (sourceRows 1354)) := by decide +kernel

theorem mergedZero1348 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1348 x = 0 := by
  rw [mergeCheck1348, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1349 : merged1349 = Integer.Sparse.merge (Integer.Sparse.scale (-431395002438401433600) (sourceRows 1356)) (Integer.Sparse.scale (-143251566798064435200) (sourceRows 1357)) := by decide +kernel

theorem mergedZero1349 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1349 x = 0 := by
  rw [mergeCheck1349, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1350 : merged1350 = Integer.Sparse.merge (Integer.Sparse.scale (5977466481711513600000) (sourceRows 1355)) merged1349 := by decide +kernel

theorem mergedZero1350 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1350 x = 0 := by
  rw [mergeCheck1350, Integer.Sparse.eval_merge]
  rw [mergedZero1349 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1351 : merged1351 = Integer.Sparse.merge merged1348 merged1350 := by decide +kernel

theorem mergedZero1351 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1351 x = 0 := by
  rw [mergeCheck1351, Integer.Sparse.eval_merge]
  rw [mergedZero1348 x h, mergedZero1350 x h]
  simp only [add_zero]

theorem mergeCheck1352 : merged1352 = Integer.Sparse.merge (Integer.Sparse.scale (29385416745503278387200) (sourceRows 1358)) (Integer.Sparse.scale (431395002438401433600) (sourceRows 1359)) := by decide +kernel

theorem mergedZero1352 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1352 x = 0 := by
  rw [mergeCheck1352, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1353 : merged1353 = Integer.Sparse.merge (Integer.Sparse.scale (27647854961525991763200) (sourceRows 1361)) (Integer.Sparse.scale (42100631588582832988800) (sourceRows 1362)) := by decide +kernel

theorem mergedZero1353 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1353 x = 0 := by
  rw [mergeCheck1353, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1354 : merged1354 = Integer.Sparse.merge (Integer.Sparse.scale (-51052583259165618345600) (sourceRows 1360)) merged1353 := by decide +kernel

theorem mergedZero1354 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1354 x = 0 := by
  rw [mergeCheck1354, Integer.Sparse.eval_merge]
  rw [mergedZero1353 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1355 : merged1355 = Integer.Sparse.merge merged1352 merged1354 := by decide +kernel

theorem mergedZero1355 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1355 x = 0 := by
  rw [mergeCheck1355, Integer.Sparse.eval_merge]
  rw [mergedZero1352 x h, mergedZero1354 x h]
  simp only [add_zero]

theorem mergeCheck1356 : merged1356 = Integer.Sparse.merge merged1351 merged1355 := by decide +kernel

theorem mergedZero1356 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1356 x = 0 := by
  rw [mergeCheck1356, Integer.Sparse.eval_merge]
  rw [mergedZero1351 x h, mergedZero1355 x h]
  simp only [add_zero]

theorem mergeCheck1357 : merged1357 = Integer.Sparse.merge merged1347 merged1356 := by decide +kernel

theorem mergedZero1357 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1357 x = 0 := by
  rw [mergeCheck1357, Integer.Sparse.eval_merge]
  rw [mergedZero1347 x h, mergedZero1356 x h]
  simp only [add_zero]

theorem mergeCheck1358 : merged1358 = Integer.Sparse.merge merged1339 merged1357 := by decide +kernel

theorem mergedZero1358 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1358 x = 0 := by
  rw [mergeCheck1358, Integer.Sparse.eval_merge]
  rw [mergedZero1339 x h, mergedZero1357 x h]
  simp only [add_zero]

theorem mergeCheck1359 : merged1359 = Integer.Sparse.merge merged1321 merged1358 := by decide +kernel

theorem mergedZero1359 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1359 x = 0 := by
  rw [mergeCheck1359, Integer.Sparse.eval_merge]
  rw [mergedZero1321 x h, mergedZero1358 x h]
  simp only [add_zero]

theorem mergeCheck1360 : merged1360 = Integer.Sparse.merge merged1284 merged1359 := by decide +kernel

theorem mergedZero1360 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1360 x = 0 := by
  rw [mergeCheck1360, Integer.Sparse.eval_merge]
  rw [mergedZero1284 x h, mergedZero1359 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1512 : merged1512 = Integer.Sparse.merge merged1360 merged1511 := by decide +kernel

theorem mergedZero1512 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1512 x = 0 := by
  rw [mergeCheck1512, Integer.Sparse.eval_merge]
  rw [mergedZero1360 x h, mergedZero1511_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1815 : merged1815 = Integer.Sparse.merge merged1512 merged1814 := by decide +kernel

theorem mergedZero1815 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1815 x = 0 := by
  rw [mergeCheck1815, Integer.Sparse.eval_merge]
  rw [mergedZero1512 x h, mergedZero1814_e x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2422 : merged2422 = Integer.Sparse.merge merged1815 merged2421 := by decide +kernel

theorem mergedZero2422 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2422 x = 0 := by
  rw [mergeCheck2422, Integer.Sparse.eval_merge]
  rw [mergedZero1815 x h, mergedZero2421_e x h]
  simp only [add_zero]

theorem mergeCheck2423 : merged2423 = Integer.Sparse.merge merged1210 merged2422 := by decide +kernel

theorem mergedZero2423 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2423 x = 0 := by
  rw [mergeCheck2423, Integer.Sparse.eval_merge]
  rw [mergedZero1210_e x h, mergedZero2422 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem finalMergeCheck : merged2423 = merged2452 := by decide +kernel

theorem targetExpressionCheck : expr2452 = targetCombination := by rfl

theorem mergeConsequence (x : Fin 3237 → ℝ) (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) :
    Integer.Combination.eval targetRows x rawCombination = Integer.Combination.eval targetRows x residualCombination := by
  have hz := mergedZero2423 x h
  rw [finalMergeCheck, mergedEval2452_e, targetExpressionCheck] at hz
  simp only [targetCombination, Integer.Combination.eval, Int.cast_neg, Int.cast_one, neg_one_mul] at hz
  linarith

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedData

/-- The checked integer identity is incompatible with a nonnegative Gram
expression and the actual uniform moment bounds. -/
theorem false_of_certificate (x : Fin 3237 → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1)
    (hsources : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0)
    (hnonneg : 0 ≤ Integer.Combination.eval targetRows x rawCombination) : False := by
  have h := mergeConsequence x hsources
  have hneg := residualNegative x hx hzero
  rw [← h] at hneg
  exact (not_lt_of_ge hnonneg) hneg

/-- A bridge to the exact, positively scaled six Gram forms discharges the
nonnegativity premise without any numerical oracle. -/
theorem false_of_gram_interpretation_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (x : Fin 3237 → ℝ) (hx : ∀ i, |x i| ≤ 1) (hzero : x 0 = 1)
    (hsources : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0)
    (hgram : Integer.Combination.eval targetRows x rawCombination =
      (denominator : ℝ) * GramNonnegative.sourceGram B) : False := by
  apply false_of_certificate x hx hzero hsources
  rw [hgram]
  exact mul_nonneg (by exact_mod_cast denominator_pos.le)
    (GramNonnegative.sourceGram_nonneg_e B hB)

end MUB6.Certificate.MixedData

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e_oai := @OAI.MUB6.Certificate.MixedData.false_of_gram_interpretation_e_oai
