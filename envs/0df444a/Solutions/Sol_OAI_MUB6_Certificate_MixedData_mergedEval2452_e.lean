-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedEval2452_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T18:03:37.758218+00:00
-- url     : https://prove2.me/submissions/92118d3a-ce29-4775-a5f2-7506d3f9a059

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E051
import Definitions.Def_OAIQ106E186
import Definitions.Def_OAIQ106E078

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block75
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2424 : merged2424 = Integer.Sparse.merge (targetRows 0) (targetRows 1) := by decide +kernel

theorem mergedEval2424 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2424 x = Integer.Combination.eval targetRows x expr2424 := by
  rw [mergeCheck2424, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2425 : merged2425 = Integer.Sparse.merge (targetRows 3) (targetRows 4) := by decide +kernel

theorem mergedEval2425 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2425 x = Integer.Combination.eval targetRows x expr2425 := by
  rw [mergeCheck2425, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2426 : merged2426 = Integer.Sparse.merge (targetRows 2) merged2425 := by decide +kernel

theorem mergedEval2426 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2426 x = Integer.Combination.eval targetRows x expr2426 := by
  rw [mergeCheck2426, Integer.Sparse.eval_merge]
  rw [mergedEval2425]
  rfl

theorem mergeCheck2427 : merged2427 = Integer.Sparse.merge merged2424 merged2426 := by decide +kernel

theorem mergedEval2427 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2427 x = Integer.Combination.eval targetRows x expr2427 := by
  rw [mergeCheck2427, Integer.Sparse.eval_merge]
  rw [mergedEval2424, mergedEval2426]
  rfl

theorem mergeCheck2428 : merged2428 = Integer.Sparse.merge (targetRows 6) (targetRows 7) := by decide +kernel

theorem mergedEval2428 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2428 x = Integer.Combination.eval targetRows x expr2428 := by
  rw [mergeCheck2428, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2429 : merged2429 = Integer.Sparse.merge (targetRows 5) merged2428 := by decide +kernel

theorem mergedEval2429 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2429 x = Integer.Combination.eval targetRows x expr2429 := by
  rw [mergeCheck2429, Integer.Sparse.eval_merge]
  rw [mergedEval2428]
  rfl

theorem mergeCheck2430 : merged2430 = Integer.Sparse.merge (targetRows 9) (targetRows 10) := by decide +kernel

theorem mergedEval2430 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2430 x = Integer.Combination.eval targetRows x expr2430 := by
  rw [mergeCheck2430, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2431 : merged2431 = Integer.Sparse.merge (targetRows 8) merged2430 := by decide +kernel

theorem mergedEval2431 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2431 x = Integer.Combination.eval targetRows x expr2431 := by
  rw [mergeCheck2431, Integer.Sparse.eval_merge]
  rw [mergedEval2430]
  rfl

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block76
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2432 : merged2432 = Integer.Sparse.merge merged2429 merged2431 := by decide +kernel

theorem mergedEval2432 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2432 x = Integer.Combination.eval targetRows x expr2432 := by
  rw [mergeCheck2432, Integer.Sparse.eval_merge]
  rw [mergedEval2429, mergedEval2431]
  rfl

theorem mergeCheck2433 : merged2433 = Integer.Sparse.merge merged2427 merged2432 := by decide +kernel

theorem mergedEval2433 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2433 x = Integer.Combination.eval targetRows x expr2433 := by
  rw [mergeCheck2433, Integer.Sparse.eval_merge]
  rw [mergedEval2427, mergedEval2432]
  rfl

theorem mergeCheck2434 : merged2434 = Integer.Sparse.merge (targetRows 12) (targetRows 13) := by decide +kernel

theorem mergedEval2434 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2434 x = Integer.Combination.eval targetRows x expr2434 := by
  rw [mergeCheck2434, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2435 : merged2435 = Integer.Sparse.merge (targetRows 11) merged2434 := by decide +kernel

theorem mergedEval2435 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2435 x = Integer.Combination.eval targetRows x expr2435 := by
  rw [mergeCheck2435, Integer.Sparse.eval_merge]
  rw [mergedEval2434]
  rfl

theorem mergeCheck2436 : merged2436 = Integer.Sparse.merge (targetRows 15) (targetRows 16) := by decide +kernel

theorem mergedEval2436 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2436 x = Integer.Combination.eval targetRows x expr2436 := by
  rw [mergeCheck2436, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2437 : merged2437 = Integer.Sparse.merge (targetRows 14) merged2436 := by decide +kernel

theorem mergedEval2437 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2437 x = Integer.Combination.eval targetRows x expr2437 := by
  rw [mergeCheck2437, Integer.Sparse.eval_merge]
  rw [mergedEval2436]
  rfl

theorem mergeCheck2438 : merged2438 = Integer.Sparse.merge merged2435 merged2437 := by decide +kernel

theorem mergedEval2438 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2438 x = Integer.Combination.eval targetRows x expr2438 := by
  rw [mergeCheck2438, Integer.Sparse.eval_merge]
  rw [mergedEval2435, mergedEval2437]
  rfl

theorem mergeCheck2439 : merged2439 = Integer.Sparse.merge (targetRows 18) (targetRows 19) := by decide +kernel

theorem mergedEval2439 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2439 x = Integer.Combination.eval targetRows x expr2439 := by
  rw [mergeCheck2439, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2440 : merged2440 = Integer.Sparse.merge (targetRows 17) merged2439 := by decide +kernel

theorem mergedEval2440 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2440 x = Integer.Combination.eval targetRows x expr2440 := by
  rw [mergeCheck2440, Integer.Sparse.eval_merge]
  rw [mergedEval2439]
  rfl

theorem mergeCheck2441 : merged2441 = Integer.Sparse.merge (targetRows 21) (targetRows 22) := by decide +kernel

theorem mergedEval2441 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2441 x = Integer.Combination.eval targetRows x expr2441 := by
  rw [mergeCheck2441, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2442 : merged2442 = Integer.Sparse.merge (targetRows 20) merged2441 := by decide +kernel

theorem mergedEval2442 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2442 x = Integer.Combination.eval targetRows x expr2442 := by
  rw [mergeCheck2442, Integer.Sparse.eval_merge]
  rw [mergedEval2441]
  rfl

theorem mergeCheck2443 : merged2443 = Integer.Sparse.merge merged2440 merged2442 := by decide +kernel

theorem mergedEval2443 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2443 x = Integer.Combination.eval targetRows x expr2443 := by
  rw [mergeCheck2443, Integer.Sparse.eval_merge]
  rw [mergedEval2440, mergedEval2442]
  rfl

theorem mergeCheck2444 : merged2444 = Integer.Sparse.merge merged2438 merged2443 := by decide +kernel

theorem mergedEval2444 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2444 x = Integer.Combination.eval targetRows x expr2444 := by
  rw [mergeCheck2444, Integer.Sparse.eval_merge]
  rw [mergedEval2438, mergedEval2443]
  rfl

theorem mergeCheck2445 : merged2445 = Integer.Sparse.merge merged2433 merged2444 := by decide +kernel

theorem mergedEval2445 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2445 x = Integer.Combination.eval targetRows x expr2445 := by
  rw [mergeCheck2445, Integer.Sparse.eval_merge]
  rw [mergedEval2433, mergedEval2444]
  rfl

theorem mergeCheck2446 : merged2446 = Integer.Sparse.merge (targetRows 24) (targetRows 25) := by decide +kernel

theorem mergedEval2446 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2446 x = Integer.Combination.eval targetRows x expr2446 := by
  rw [mergeCheck2446, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2447 : merged2447 = Integer.Sparse.merge (targetRows 23) merged2446 := by decide +kernel

theorem mergedEval2447 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2447 x = Integer.Combination.eval targetRows x expr2447 := by
  rw [mergeCheck2447, Integer.Sparse.eval_merge]
  rw [mergedEval2446]
  rfl

theorem mergeCheck2448 : merged2448 = Integer.Sparse.merge (targetRows 27) (targetRows 28) := by decide +kernel

theorem mergedEval2448 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2448 x = Integer.Combination.eval targetRows x expr2448 := by
  rw [mergeCheck2448, Integer.Sparse.eval_merge]
  rfl

theorem mergeCheck2449 : merged2449 = Integer.Sparse.merge (targetRows 26) merged2448 := by decide +kernel

theorem mergedEval2449 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2449 x = Integer.Combination.eval targetRows x expr2449 := by
  rw [mergeCheck2449, Integer.Sparse.eval_merge]
  rw [mergedEval2448]
  rfl

theorem mergeCheck2450 : merged2450 = Integer.Sparse.merge merged2447 merged2449 := by decide +kernel

theorem mergedEval2450 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2450 x = Integer.Combination.eval targetRows x expr2450 := by
  rw [mergeCheck2450, Integer.Sparse.eval_merge]
  rw [mergedEval2447, mergedEval2449]
  rfl

theorem mergeCheck2451 : merged2451 = Integer.Sparse.scale (-1) merged2450 := by decide +kernel

theorem mergedEval2451 (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2451 x = Integer.Combination.eval targetRows x expr2451 := by
  rw [mergeCheck2451, Integer.Sparse.eval_scale, mergedEval2450]
  rfl

theorem mergeCheck2452 : merged2452 = Integer.Sparse.merge merged2445 merged2451 := by decide +kernel

theorem mergedEval2452_e_oai (x : Fin 3237 → ℝ) :
    Integer.Sparse.eval merged2452 x = Integer.Combination.eval targetRows x expr2452 := by
  rw [mergeCheck2452, Integer.Sparse.eval_merge]
  rw [mergedEval2445, mergedEval2451]
  rfl

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedEval2452_e_oai := @OAI.MUB6.Certificate.MixedData.mergedEval2452_e_oai
