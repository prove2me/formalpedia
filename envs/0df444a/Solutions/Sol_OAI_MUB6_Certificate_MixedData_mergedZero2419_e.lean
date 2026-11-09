-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero2419_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:24:50.778935+00:00
-- url     : https://prove2.me/submissions/aeaa4dae-1266-4a39-8318-8c43b6d026c7

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E077

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2269 : merged2269 = Integer.Sparse.merge (Integer.Sparse.scale (-51360480000000) (sourceRows 2273)) (Integer.Sparse.scale (-1438093440000) (sourceRows 2274)) := by decide +kernel

theorem mergedZero2269 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2269 x = 0 := by
  rw [mergeCheck2269, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2270 : merged2270 = Integer.Sparse.merge (Integer.Sparse.scale (-1095690240000) (sourceRows 2275)) (Integer.Sparse.scale (65433251520000) (sourceRows 2276)) := by decide +kernel

theorem mergedZero2270 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2270 x = 0 := by
  rw [mergeCheck2270, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2271 : merged2271 = Integer.Sparse.merge merged2269 merged2270 := by decide +kernel

theorem mergedZero2271 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2271 x = 0 := by
  rw [mergeCheck2271, Integer.Sparse.eval_merge]
  rw [mergedZero2269 x h, mergedZero2270 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block71
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2272 : merged2272 = Integer.Sparse.merge (Integer.Sparse.scale (6574141440000) (sourceRows 2277)) (Integer.Sparse.scale (5136048000000) (sourceRows 2278)) := by decide +kernel

theorem mergedZero2272 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2272 x = 0 := by
  rw [mergeCheck2272, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2273 : merged2273 = Integer.Sparse.merge (Integer.Sparse.scale (2191380480000) (sourceRows 2280)) (Integer.Sparse.scale (-5546931840000) (sourceRows 2281)) := by decide +kernel

theorem mergedZero2273 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2273 x = 0 := by
  rw [mergeCheck2273, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2274 : merged2274 = Integer.Sparse.merge (Integer.Sparse.scale (7190467200000) (sourceRows 2279)) merged2273 := by decide +kernel

theorem mergedZero2274 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2274 x = 0 := by
  rw [mergeCheck2274, Integer.Sparse.eval_merge]
  rw [mergedZero2273 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2275 : merged2275 = Integer.Sparse.merge merged2272 merged2274 := by decide +kernel

theorem mergedZero2275 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2275 x = 0 := by
  rw [mergeCheck2275, Integer.Sparse.eval_merge]
  rw [mergedZero2272 x h, mergedZero2274 x h]
  simp only [add_zero]

theorem mergeCheck2276 : merged2276 = Integer.Sparse.merge merged2271 merged2275 := by decide +kernel

theorem mergedZero2276 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2276 x = 0 := by
  rw [mergeCheck2276, Integer.Sparse.eval_merge]
  rw [mergedZero2271 x h, mergedZero2275 x h]
  simp only [add_zero]

theorem mergeCheck2277 : merged2277 = Integer.Sparse.merge (Integer.Sparse.scale (616325760000) (sourceRows 2282)) (Integer.Sparse.scale (279811895040000) (sourceRows 2283)) := by decide +kernel

theorem mergedZero2277 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2277 x = 0 := by
  rw [mergeCheck2277, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2278 : merged2278 = Integer.Sparse.merge (Integer.Sparse.scale (-407802211200000) (sourceRows 2285)) (Integer.Sparse.scale (-40882942080000) (sourceRows 2286)) := by decide +kernel

theorem mergedZero2278 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2278 x = 0 := by
  rw [mergeCheck2278, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2279 : merged2279 = Integer.Sparse.merge (Integer.Sparse.scale (-59680877760000) (sourceRows 2284)) merged2278 := by decide +kernel

theorem mergedZero2279 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2279 x = 0 := by
  rw [mergeCheck2279, Integer.Sparse.eval_merge]
  rw [mergedZero2278 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2280 : merged2280 = Integer.Sparse.merge merged2277 merged2279 := by decide +kernel

theorem mergedZero2280 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2280 x = 0 := by
  rw [mergeCheck2280, Integer.Sparse.eval_merge]
  rw [mergedZero2277 x h, mergedZero2279 x h]
  simp only [add_zero]

theorem mergeCheck2281 : merged2281 = Integer.Sparse.merge (Integer.Sparse.scale (330350607360000) (sourceRows 2287)) (Integer.Sparse.scale (4930606080000) (sourceRows 2288)) := by decide +kernel

theorem mergedZero2281 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2281 x = 0 := by
  rw [mergeCheck2281, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2282 : merged2282 = Integer.Sparse.merge (Integer.Sparse.scale (-3697954560000) (sourceRows 2290)) (Integer.Sparse.scale (169489584000000) (sourceRows 2291)) := by decide +kernel

theorem mergedZero2282 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2282 x = 0 := by
  rw [mergeCheck2282, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2283 : merged2283 = Integer.Sparse.merge (Integer.Sparse.scale (6574141440000) (sourceRows 2289)) merged2282 := by decide +kernel

theorem mergedZero2283 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2283 x = 0 := by
  rw [mergeCheck2283, Integer.Sparse.eval_merge]
  rw [mergedZero2282 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2284 : merged2284 = Integer.Sparse.merge merged2281 merged2283 := by decide +kernel

theorem mergedZero2284 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2284 x = 0 := by
  rw [mergeCheck2284, Integer.Sparse.eval_merge]
  rw [mergedZero2281 x h, mergedZero2283 x h]
  simp only [add_zero]

theorem mergeCheck2285 : merged2285 = Integer.Sparse.merge merged2280 merged2284 := by decide +kernel

theorem mergedZero2285 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2285 x = 0 := by
  rw [mergeCheck2285, Integer.Sparse.eval_merge]
  rw [mergedZero2280 x h, mergedZero2284 x h]
  simp only [add_zero]

theorem mergeCheck2286 : merged2286 = Integer.Sparse.merge merged2276 merged2285 := by decide +kernel

theorem mergedZero2286 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2286 x = 0 := by
  rw [mergeCheck2286, Integer.Sparse.eval_merge]
  rw [mergedZero2276 x h, mergedZero2285 x h]
  simp only [add_zero]

theorem mergeCheck2287 : merged2287 = Integer.Sparse.merge (Integer.Sparse.scale (59680877760000) (sourceRows 2292)) (Integer.Sparse.scale (-65433251520000) (sourceRows 2293)) := by decide +kernel

theorem mergedZero2287 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2287 x = 0 := by
  rw [mergeCheck2287, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2288 : merged2288 = Integer.Sparse.merge (Integer.Sparse.scale (-156957626880000) (sourceRows 2294)) (Integer.Sparse.scale (-51360480000000) (sourceRows 2295)) := by decide +kernel

theorem mergedZero2288 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2288 x = 0 := by
  rw [mergeCheck2288, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2289 : merged2289 = Integer.Sparse.merge merged2287 merged2288 := by decide +kernel

theorem mergedZero2289 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2289 x = 0 := by
  rw [mergeCheck2289, Integer.Sparse.eval_merge]
  rw [mergedZero2287 x h, mergedZero2288 x h]
  simp only [add_zero]

theorem mergeCheck2290 : merged2290 = Integer.Sparse.merge (Integer.Sparse.scale (51360480000000) (sourceRows 2296)) (Integer.Sparse.scale (-1232651520000) (sourceRows 2297)) := by decide +kernel

theorem mergedZero2290 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2290 x = 0 := by
  rw [mergeCheck2290, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2291 : merged2291 = Integer.Sparse.merge (Integer.Sparse.scale (8217676800000) (sourceRows 2299)) (Integer.Sparse.scale (-35336010240000) (sourceRows 2300)) := by decide +kernel

theorem mergedZero2291 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2291 x = 0 := by
  rw [mergeCheck2291, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2292 : merged2292 = Integer.Sparse.merge (Integer.Sparse.scale (116896452480000) (sourceRows 2298)) merged2291 := by decide +kernel

theorem mergedZero2292 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2292 x = 0 := by
  rw [mergeCheck2292, Integer.Sparse.eval_merge]
  rw [mergedZero2291 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2293 : merged2293 = Integer.Sparse.merge merged2290 merged2292 := by decide +kernel

theorem mergedZero2293 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2293 x = 0 := by
  rw [mergeCheck2293, Integer.Sparse.eval_merge]
  rw [mergedZero2290 x h, mergedZero2292 x h]
  simp only [add_zero]

theorem mergeCheck2294 : merged2294 = Integer.Sparse.merge merged2289 merged2293 := by decide +kernel

theorem mergedZero2294 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2294 x = 0 := by
  rw [mergeCheck2294, Integer.Sparse.eval_merge]
  rw [mergedZero2289 x h, mergedZero2293 x h]
  simp only [add_zero]

theorem mergeCheck2295 : merged2295 = Integer.Sparse.merge (Integer.Sparse.scale (-36979545600000) (sourceRows 2301)) (Integer.Sparse.scale (114961874400000) (sourceRows 2302)) := by decide +kernel

theorem mergedZero2295 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2295 x = 0 := by
  rw [mergeCheck2295, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2296 : merged2296 = Integer.Sparse.merge (Integer.Sparse.scale (4793644800000) (sourceRows 2304)) (Integer.Sparse.scale (104450096160000) (sourceRows 2305)) := by decide +kernel

theorem mergedZero2296 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2296 x = 0 := by
  rw [mergeCheck2296, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2297 : merged2297 = Integer.Sparse.merge (Integer.Sparse.scale (-6916544640000) (sourceRows 2303)) merged2296 := by decide +kernel

theorem mergedZero2297 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2297 x = 0 := by
  rw [mergeCheck2297, Integer.Sparse.eval_merge]
  rw [mergedZero2296 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2298 : merged2298 = Integer.Sparse.merge merged2295 merged2297 := by decide +kernel

theorem mergedZero2298 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2298 x = 0 := by
  rw [mergeCheck2298, Integer.Sparse.eval_merge]
  rw [mergedZero2295 x h, mergedZero2297 x h]
  simp only [add_zero]

theorem mergeCheck2299 : merged2299 = Integer.Sparse.merge (Integer.Sparse.scale (-16315512480000) (sourceRows 2306)) (Integer.Sparse.scale (14997260160000) (sourceRows 2307)) := by decide +kernel

theorem mergedZero2299 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2299 x = 0 := by
  rw [mergeCheck2299, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2300 : merged2300 = Integer.Sparse.merge (Integer.Sparse.scale (16897597920000) (sourceRows 2309)) (Integer.Sparse.scale (-19362900960000) (sourceRows 2310)) := by decide +kernel

theorem mergedZero2300 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2300 x = 0 := by
  rw [mergeCheck2300, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2301 : merged2301 = Integer.Sparse.merge (Integer.Sparse.scale (-82228128480000) (sourceRows 2308)) merged2300 := by decide +kernel

theorem mergedZero2301 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2301 x = 0 := by
  rw [mergeCheck2301, Integer.Sparse.eval_merge]
  rw [mergedZero2300 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2302 : merged2302 = Integer.Sparse.merge merged2299 merged2301 := by decide +kernel

theorem mergedZero2302 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2302 x = 0 := by
  rw [mergeCheck2302, Integer.Sparse.eval_merge]
  rw [mergedZero2299 x h, mergedZero2301 x h]
  simp only [add_zero]

theorem mergeCheck2303 : merged2303 = Integer.Sparse.merge merged2298 merged2302 := by decide +kernel

theorem mergedZero2303 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2303 x = 0 := by
  rw [mergeCheck2303, Integer.Sparse.eval_merge]
  rw [mergedZero2298 x h, mergedZero2302 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2304 : merged2304 = Integer.Sparse.merge merged2294 merged2303 := by decide +kernel

theorem mergedZero2304 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2304 x = 0 := by
  rw [mergeCheck2304, Integer.Sparse.eval_merge]
  rw [mergedZero2294 x h, mergedZero2303 x h]
  simp only [add_zero]

theorem mergeCheck2305 : merged2305 = Integer.Sparse.merge merged2286 merged2304 := by decide +kernel

theorem mergedZero2305 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2305 x = 0 := by
  rw [mergeCheck2305, Integer.Sparse.eval_merge]
  rw [mergedZero2286 x h, mergedZero2304 x h]
  simp only [add_zero]

theorem mergeCheck2306 : merged2306 = Integer.Sparse.merge (Integer.Sparse.scale (-513604800000) (sourceRows 2311)) (Integer.Sparse.scale (2054419200000) (sourceRows 2312)) := by decide +kernel

theorem mergedZero2306 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2306 x = 0 := by
  rw [mergeCheck2306, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2307 : merged2307 = Integer.Sparse.merge (Integer.Sparse.scale (-57112853760000) (sourceRows 2313)) (Integer.Sparse.scale (-1129930560000) (sourceRows 2314)) := by decide +kernel

theorem mergedZero2307 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2307 x = 0 := by
  rw [mergeCheck2307, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2308 : merged2308 = Integer.Sparse.merge merged2306 merged2307 := by decide +kernel

theorem mergedZero2308 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2308 x = 0 := by
  rw [mergeCheck2308, Integer.Sparse.eval_merge]
  rw [mergedZero2306 x h, mergedZero2307 x h]
  simp only [add_zero]

theorem mergeCheck2309 : merged2309 = Integer.Sparse.merge (Integer.Sparse.scale (12942840960000) (sourceRows 2315)) (Integer.Sparse.scale (-305653368981657600000) (sourceRows 2316)) := by decide +kernel

theorem mergedZero2309 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2309 x = 0 := by
  rw [mergeCheck2309, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2310 : merged2310 = Integer.Sparse.merge (Integer.Sparse.scale (5786640343802880000) (sourceRows 2318)) (Integer.Sparse.scale (107363412599466240000) (sourceRows 2319)) := by decide +kernel

theorem mergedZero2310 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2310 x = 0 := by
  rw [mergeCheck2310, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2311 : merged2311 = Integer.Sparse.merge (Integer.Sparse.scale (-42789140967962880000) (sourceRows 2317)) merged2310 := by decide +kernel

theorem mergedZero2311 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2311 x = 0 := by
  rw [mergeCheck2311, Integer.Sparse.eval_merge]
  rw [mergedZero2310 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2312 : merged2312 = Integer.Sparse.merge merged2309 merged2311 := by decide +kernel

theorem mergedZero2312 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2312 x = 0 := by
  rw [mergeCheck2312, Integer.Sparse.eval_merge]
  rw [mergedZero2309 x h, mergedZero2311 x h]
  simp only [add_zero]

theorem mergeCheck2313 : merged2313 = Integer.Sparse.merge merged2308 merged2312 := by decide +kernel

theorem mergedZero2313 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2313 x = 0 := by
  rw [mergeCheck2313, Integer.Sparse.eval_merge]
  rw [mergedZero2308 x h, mergedZero2312 x h]
  simp only [add_zero]

theorem mergeCheck2314 : merged2314 = Integer.Sparse.merge (Integer.Sparse.scale (-77188863848140800000) (sourceRows 2320)) (Integer.Sparse.scale (16456910625642240000) (sourceRows 2321)) := by decide +kernel

theorem mergedZero2314 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2314 x = 0 := by
  rw [mergeCheck2314, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2315 : merged2315 = Integer.Sparse.merge (Integer.Sparse.scale (27420299965139040000) (sourceRows 2323)) (Integer.Sparse.scale (-11573271237277440000) (sourceRows 2324)) := by decide +kernel

theorem mergedZero2315 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2315 x = 0 := by
  rw [mergeCheck2315, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2316 : merged2316 = Integer.Sparse.merge (Integer.Sparse.scale (-34317733451142240000) (sourceRows 2322)) merged2315 := by decide +kernel

theorem mergedZero2316 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2316 x = 0 := by
  rw [mergeCheck2316, Integer.Sparse.eval_merge]
  rw [mergedZero2315 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2317 : merged2317 = Integer.Sparse.merge merged2314 merged2316 := by decide +kernel

theorem mergedZero2317 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2317 x = 0 := by
  rw [mergeCheck2317, Integer.Sparse.eval_merge]
  rw [mergedZero2314 x h, mergedZero2316 x h]
  simp only [add_zero]

theorem mergeCheck2318 : merged2318 = Integer.Sparse.merge (Integer.Sparse.scale (-37917942684344640000) (sourceRows 2325)) (Integer.Sparse.scale (92901847701196800000) (sourceRows 2326)) := by decide +kernel

theorem mergedZero2318 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2318 x = 0 := by
  rw [mergeCheck2318, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2319 : merged2319 = Integer.Sparse.merge (Integer.Sparse.scale (66768624000000) (sourceRows 2328)) (Integer.Sparse.scale (-414307872000000) (sourceRows 2329)) := by decide +kernel

theorem mergedZero2319 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2319 x = 0 := by
  rw [mergeCheck2319, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2320 : merged2320 = Integer.Sparse.merge (Integer.Sparse.scale (48874909008844800000) (sourceRows 2327)) merged2319 := by decide +kernel

theorem mergedZero2320 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2320 x = 0 := by
  rw [mergeCheck2320, Integer.Sparse.eval_merge]
  rw [mergedZero2319 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2321 : merged2321 = Integer.Sparse.merge merged2318 merged2320 := by decide +kernel

theorem mergedZero2321 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2321 x = 0 := by
  rw [mergeCheck2321, Integer.Sparse.eval_merge]
  rw [mergedZero2318 x h, mergedZero2320 x h]
  simp only [add_zero]

theorem mergeCheck2322 : merged2322 = Integer.Sparse.merge merged2317 merged2321 := by decide +kernel

theorem mergedZero2322 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2322 x = 0 := by
  rw [mergeCheck2322, Integer.Sparse.eval_merge]
  rw [mergedZero2317 x h, mergedZero2321 x h]
  simp only [add_zero]

theorem mergeCheck2323 : merged2323 = Integer.Sparse.merge merged2313 merged2322 := by decide +kernel

theorem mergedZero2323 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2323 x = 0 := by
  rw [mergeCheck2323, Integer.Sparse.eval_merge]
  rw [mergedZero2313 x h, mergedZero2322 x h]
  simp only [add_zero]

theorem mergeCheck2324 : merged2324 = Integer.Sparse.merge (Integer.Sparse.scale (-30040174080000) (sourceRows 2330)) (Integer.Sparse.scale (65741414400000) (sourceRows 2331)) := by decide +kernel

theorem mergedZero2324 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2324 x = 0 := by
  rw [mergeCheck2324, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2325 : merged2325 = Integer.Sparse.merge (Integer.Sparse.scale (9039444480000) (sourceRows 2332)) (Integer.Sparse.scale (-27118333440000) (sourceRows 2333)) := by decide +kernel

theorem mergedZero2325 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2325 x = 0 := by
  rw [mergeCheck2325, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2326 : merged2326 = Integer.Sparse.merge merged2324 merged2325 := by decide +kernel

theorem mergedZero2326 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2326 x = 0 := by
  rw [mergeCheck2326, Integer.Sparse.eval_merge]
  rw [mergedZero2324 x h, mergedZero2325 x h]
  simp only [add_zero]

theorem mergeCheck2327 : merged2327 = Integer.Sparse.merge (Integer.Sparse.scale (21365959680000) (sourceRows 2334)) (Integer.Sparse.scale (-3595233600000) (sourceRows 2335)) := by decide +kernel

theorem mergedZero2327 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2327 x = 0 := by
  rw [mergeCheck2327, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2328 : merged2328 = Integer.Sparse.merge (Integer.Sparse.scale (16538074560000) (sourceRows 2337)) (Integer.Sparse.scale (-56496528000000) (sourceRows 2338)) := by decide +kernel

theorem mergedZero2328 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2328 x = 0 := by
  rw [mergeCheck2328, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2329 : merged2329 = Integer.Sparse.merge (Integer.Sparse.scale (-3030268320000) (sourceRows 2336)) merged2328 := by decide +kernel

theorem mergedZero2329 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2329 x = 0 := by
  rw [mergeCheck2329, Integer.Sparse.eval_merge]
  rw [mergedZero2328 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2330 : merged2330 = Integer.Sparse.merge merged2327 merged2329 := by decide +kernel

theorem mergedZero2330 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2330 x = 0 := by
  rw [mergeCheck2330, Integer.Sparse.eval_merge]
  rw [mergedZero2327 x h, mergedZero2329 x h]
  simp only [add_zero]

theorem mergeCheck2331 : merged2331 = Integer.Sparse.merge merged2326 merged2330 := by decide +kernel

theorem mergedZero2331 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2331 x = 0 := by
  rw [mergeCheck2331, Integer.Sparse.eval_merge]
  rw [mergedZero2326 x h, mergedZero2330 x h]
  simp only [add_zero]

theorem mergeCheck2332 : merged2332 = Integer.Sparse.merge (Integer.Sparse.scale (-39033964800000) (sourceRows 2339)) (Integer.Sparse.scale (-3287070720000) (sourceRows 2340)) := by decide +kernel

theorem mergedZero2332 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2332 x = 0 := by
  rw [mergeCheck2332, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2333 : merged2333 = Integer.Sparse.merge (Integer.Sparse.scale (9244886400000) (sourceRows 2342)) (Integer.Sparse.scale (6163257600000) (sourceRows 2343)) := by decide +kernel

theorem mergedZero2333 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2333 x = 0 := by
  rw [mergeCheck2333, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2334 : merged2334 = Integer.Sparse.merge (Integer.Sparse.scale (-12531957120000) (sourceRows 2341)) merged2333 := by decide +kernel

theorem mergedZero2334 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2334 x = 0 := by
  rw [mergeCheck2334, Integer.Sparse.eval_merge]
  rw [mergedZero2333 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2335 : merged2335 = Integer.Sparse.merge merged2332 merged2334 := by decide +kernel

theorem mergedZero2335 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2335 x = 0 := by
  rw [mergeCheck2335, Integer.Sparse.eval_merge]
  rw [mergedZero2332 x h, mergedZero2334 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2336 : merged2336 = Integer.Sparse.merge (Integer.Sparse.scale (-17719365600000) (sourceRows 2344)) (Integer.Sparse.scale (-27169693920000) (sourceRows 2345)) := by decide +kernel

theorem mergedZero2336 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2336 x = 0 := by
  rw [mergeCheck2336, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2337 : merged2337 = Integer.Sparse.merge (Integer.Sparse.scale (27169693920000) (sourceRows 2347)) (Integer.Sparse.scale (205441920000) (sourceRows 2348)) := by decide +kernel

theorem mergedZero2337 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2337 x = 0 := by
  rw [mergeCheck2337, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2338 : merged2338 = Integer.Sparse.merge (Integer.Sparse.scale (88596828000000) (sourceRows 2346)) merged2337 := by decide +kernel

theorem mergedZero2338 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2338 x = 0 := by
  rw [mergeCheck2338, Integer.Sparse.eval_merge]
  rw [mergedZero2337 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2339 : merged2339 = Integer.Sparse.merge merged2336 merged2338 := by decide +kernel

theorem mergedZero2339 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2339 x = 0 := by
  rw [mergeCheck2339, Integer.Sparse.eval_merge]
  rw [mergedZero2336 x h, mergedZero2338 x h]
  simp only [add_zero]

theorem mergeCheck2340 : merged2340 = Integer.Sparse.merge merged2335 merged2339 := by decide +kernel

theorem mergedZero2340 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2340 x = 0 := by
  rw [mergeCheck2340, Integer.Sparse.eval_merge]
  rw [mergedZero2335 x h, mergedZero2339 x h]
  simp only [add_zero]

theorem mergeCheck2341 : merged2341 = Integer.Sparse.merge merged2331 merged2340 := by decide +kernel

theorem mergedZero2341 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2341 x = 0 := by
  rw [mergeCheck2341, Integer.Sparse.eval_merge]
  rw [mergedZero2331 x h, mergedZero2340 x h]
  simp only [add_zero]

theorem mergeCheck2342 : merged2342 = Integer.Sparse.merge merged2323 merged2341 := by decide +kernel

theorem mergedZero2342 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2342 x = 0 := by
  rw [mergeCheck2342, Integer.Sparse.eval_merge]
  rw [mergedZero2323 x h, mergedZero2341 x h]
  simp only [add_zero]

theorem mergeCheck2343 : merged2343 = Integer.Sparse.merge merged2305 merged2342 := by decide +kernel

theorem mergedZero2343 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2343 x = 0 := by
  rw [mergeCheck2343, Integer.Sparse.eval_merge]
  rw [mergedZero2305 x h, mergedZero2342 x h]
  simp only [add_zero]

theorem mergeCheck2344 : merged2344 = Integer.Sparse.merge (Integer.Sparse.scale (-205441920000) (sourceRows 2349)) (Integer.Sparse.scale (-17976168000000) (sourceRows 2350)) := by decide +kernel

theorem mergedZero2344 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2344 x = 0 := by
  rw [mergeCheck2344, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2345 : merged2345 = Integer.Sparse.merge (Integer.Sparse.scale (4108838400000) (sourceRows 2351)) (Integer.Sparse.scale (1232651520000) (sourceRows 2352)) := by decide +kernel

theorem mergedZero2345 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2345 x = 0 := by
  rw [mergeCheck2345, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2346 : merged2346 = Integer.Sparse.merge merged2344 merged2345 := by decide +kernel

theorem mergedZero2346 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2346 x = 0 := by
  rw [mergeCheck2346, Integer.Sparse.eval_merge]
  rw [mergedZero2344 x h, mergedZero2345 x h]
  simp only [add_zero]

theorem mergeCheck2347 : merged2347 = Integer.Sparse.merge (Integer.Sparse.scale (23945397120000) (sourceRows 2353)) (Integer.Sparse.scale (1209824640000) (sourceRows 2354)) := by decide +kernel

theorem mergedZero2347 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2347 x = 0 := by
  rw [mergeCheck2347, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2348 : merged2348 = Integer.Sparse.merge (Integer.Sparse.scale (-4519722240000) (sourceRows 2356)) (Integer.Sparse.scale (-9039444480000) (sourceRows 2357)) := by decide +kernel

theorem mergedZero2348 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2348 x = 0 := by
  rw [mergeCheck2348, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2349 : merged2349 = Integer.Sparse.merge (Integer.Sparse.scale (4108838400000) (sourceRows 2355)) merged2348 := by decide +kernel

theorem mergedZero2349 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2349 x = 0 := by
  rw [mergeCheck2349, Integer.Sparse.eval_merge]
  rw [mergedZero2348 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2350 : merged2350 = Integer.Sparse.merge merged2347 merged2349 := by decide +kernel

theorem mergedZero2350 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2350 x = 0 := by
  rw [mergeCheck2350, Integer.Sparse.eval_merge]
  rw [mergedZero2347 x h, mergedZero2349 x h]
  simp only [add_zero]

theorem mergeCheck2351 : merged2351 = Integer.Sparse.merge merged2346 merged2350 := by decide +kernel

theorem mergedZero2351 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2351 x = 0 := by
  rw [mergeCheck2351, Integer.Sparse.eval_merge]
  rw [mergedZero2346 x h, mergedZero2350 x h]
  simp only [add_zero]

theorem mergeCheck2352 : merged2352 = Integer.Sparse.merge (Integer.Sparse.scale (-9450328320000) (sourceRows 2358)) (Integer.Sparse.scale (1643535360000) (sourceRows 2359)) := by decide +kernel

theorem mergedZero2352 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2352 x = 0 := by
  rw [mergeCheck2352, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2353 : merged2353 = Integer.Sparse.merge (Integer.Sparse.scale (18078888960000) (sourceRows 2361)) (Integer.Sparse.scale (-9039444480000) (sourceRows 2362)) := by decide +kernel

theorem mergedZero2353 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2353 x = 0 := by
  rw [mergeCheck2353, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2354 : merged2354 = Integer.Sparse.merge (Integer.Sparse.scale (-4108838400000) (sourceRows 2360)) merged2353 := by decide +kernel

theorem mergedZero2354 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2354 x = 0 := by
  rw [mergeCheck2354, Integer.Sparse.eval_merge]
  rw [mergedZero2353 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2355 : merged2355 = Integer.Sparse.merge merged2352 merged2354 := by decide +kernel

theorem mergedZero2355 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2355 x = 0 := by
  rw [mergeCheck2355, Integer.Sparse.eval_merge]
  rw [mergedZero2352 x h, mergedZero2354 x h]
  simp only [add_zero]

theorem mergeCheck2356 : merged2356 = Integer.Sparse.merge (Integer.Sparse.scale (-1232651520000) (sourceRows 2363)) (Integer.Sparse.scale (-23077975680000) (sourceRows 2364)) := by decide +kernel

theorem mergedZero2356 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2356 x = 0 := by
  rw [mergeCheck2356, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2357 : merged2357 = Integer.Sparse.merge (Integer.Sparse.scale (-5478451200000) (sourceRows 2366)) (Integer.Sparse.scale (53414899200000) (sourceRows 2367)) := by decide +kernel

theorem mergedZero2357 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2357 x = 0 := by
  rw [mergeCheck2357, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2358 : merged2358 = Integer.Sparse.merge (Integer.Sparse.scale (3287070720000) (sourceRows 2365)) merged2357 := by decide +kernel

theorem mergedZero2358 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2358 x = 0 := by
  rw [mergeCheck2358, Integer.Sparse.eval_merge]
  rw [mergedZero2357 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2359 : merged2359 = Integer.Sparse.merge merged2356 merged2358 := by decide +kernel

theorem mergedZero2359 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2359 x = 0 := by
  rw [mergeCheck2359, Integer.Sparse.eval_merge]
  rw [mergedZero2356 x h, mergedZero2358 x h]
  simp only [add_zero]

theorem mergeCheck2360 : merged2360 = Integer.Sparse.merge merged2355 merged2359 := by decide +kernel

theorem mergedZero2360 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2360 x = 0 := by
  rw [mergeCheck2360, Integer.Sparse.eval_merge]
  rw [mergedZero2355 x h, mergedZero2359 x h]
  simp only [add_zero]

theorem mergeCheck2361 : merged2361 = Integer.Sparse.merge merged2351 merged2360 := by decide +kernel

theorem mergedZero2361 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2361 x = 0 := by
  rw [mergeCheck2361, Integer.Sparse.eval_merge]
  rw [mergedZero2351 x h, mergedZero2360 x h]
  simp only [add_zero]

theorem mergeCheck2362 : merged2362 = Integer.Sparse.merge (Integer.Sparse.scale (-25611759360000) (sourceRows 2368)) (Integer.Sparse.scale (-24858472320000) (sourceRows 2369)) := by decide +kernel

theorem mergedZero2362 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2362 x = 0 := by
  rw [mergeCheck2362, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2363 : merged2363 = Integer.Sparse.merge (Integer.Sparse.scale (-6049123200000) (sourceRows 2370)) (Integer.Sparse.scale (74301494400000) (sourceRows 2371)) := by decide +kernel

theorem mergedZero2363 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2363 x = 0 := by
  rw [mergeCheck2363, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2364 : merged2364 = Integer.Sparse.merge merged2362 merged2363 := by decide +kernel

theorem mergedZero2364 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2364 x = 0 := by
  rw [mergeCheck2364, Integer.Sparse.eval_merge]
  rw [mergedZero2362 x h, mergedZero2363 x h]
  simp only [add_zero]

theorem mergeCheck2365 : merged2365 = Integer.Sparse.merge (Integer.Sparse.scale (890248320000) (sourceRows 2372)) (Integer.Sparse.scale (219138048000000) (sourceRows 2373)) := by decide +kernel

theorem mergedZero2365 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2365 x = 0 := by
  rw [mergeCheck2365, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2366 : merged2366 = Integer.Sparse.merge (Integer.Sparse.scale (45197222400000) (sourceRows 2375)) (Integer.Sparse.scale (5341489920000) (sourceRows 2376)) := by decide +kernel

theorem mergedZero2366 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2366 x = 0 := by
  rw [mergeCheck2366, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2367 : merged2367 = Integer.Sparse.merge (Integer.Sparse.scale (23968224000000) (sourceRows 2374)) merged2366 := by decide +kernel

theorem mergedZero2367 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2367 x = 0 := by
  rw [mergeCheck2367, Integer.Sparse.eval_merge]
  rw [mergedZero2366 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck2368 : merged2368 = Integer.Sparse.merge merged2365 merged2367 := by decide +kernel

theorem mergedZero2368 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2368 x = 0 := by
  rw [mergeCheck2368, Integer.Sparse.eval_merge]
  rw [mergedZero2365 x h, mergedZero2367 x h]
  simp only [add_zero]

theorem mergeCheck2369 : merged2369 = Integer.Sparse.merge merged2364 merged2368 := by decide +kernel

theorem mergedZero2369 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2369 x = 0 := by
  rw [mergeCheck2369, Integer.Sparse.eval_merge]
  rw [mergedZero2364 x h, mergedZero2368 x h]
  simp only [add_zero]

theorem mergeCheck2370 : merged2370 = Integer.Sparse.merge (Integer.Sparse.scale (-8217676800000) (sourceRows 2377)) (Integer.Sparse.scale (24516069120000) (sourceRows 2378)) := by decide +kernel

theorem mergedZero2370 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2370 x = 0 := by
  rw [mergeCheck2370, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2371 : merged2371 = Integer.Sparse.merge (Integer.Sparse.scale (-51874084800000) (sourceRows 2380)) (Integer.Sparse.scale (3287070720000) (sourceRows 2381)) := by decide +kernel

theorem mergedZero2371 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2371 x = 0 := by
  rw [mergeCheck2371, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2372 : merged2372 = Integer.Sparse.merge (Integer.Sparse.scale (-27255294720000) (sourceRows 2379)) merged2371 := by decide +kernel

theorem mergedZero2372 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2372 x = 0 := by
  rw [mergeCheck2372, Integer.Sparse.eval_merge]
  rw [mergedZero2371 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2373 : merged2373 = Integer.Sparse.merge merged2370 merged2372 := by decide +kernel

theorem mergedZero2373 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2373 x = 0 := by
  rw [mergeCheck2373, Integer.Sparse.eval_merge]
  rw [mergedZero2370 x h, mergedZero2372 x h]
  simp only [add_zero]

theorem mergeCheck2374 : merged2374 = Integer.Sparse.merge (Integer.Sparse.scale (-4793644800000) (sourceRows 2382)) (Integer.Sparse.scale (-32596784640000) (sourceRows 2383)) := by decide +kernel

theorem mergedZero2374 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2374 x = 0 := by
  rw [mergeCheck2374, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2375 : merged2375 = Integer.Sparse.merge (Integer.Sparse.scale (109226620800000) (sourceRows 2385)) (Integer.Sparse.scale (24789991680000) (sourceRows 2386)) := by decide +kernel

theorem mergedZero2375 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2375 x = 0 := by
  rw [mergeCheck2375, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2376 : merged2376 = Integer.Sparse.merge (Integer.Sparse.scale (4108838400000) (sourceRows 2384)) merged2375 := by decide +kernel

theorem mergedZero2376 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2376 x = 0 := by
  rw [mergeCheck2376, Integer.Sparse.eval_merge]
  rw [mergedZero2375 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2377 : merged2377 = Integer.Sparse.merge merged2374 merged2376 := by decide +kernel

theorem mergedZero2377 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2377 x = 0 := by
  rw [mergeCheck2377, Integer.Sparse.eval_merge]
  rw [mergedZero2374 x h, mergedZero2376 x h]
  simp only [add_zero]

theorem mergeCheck2378 : merged2378 = Integer.Sparse.merge merged2373 merged2377 := by decide +kernel

theorem mergedZero2378 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2378 x = 0 := by
  rw [mergeCheck2378, Integer.Sparse.eval_merge]
  rw [mergedZero2373 x h, mergedZero2377 x h]
  simp only [add_zero]

theorem mergeCheck2379 : merged2379 = Integer.Sparse.merge merged2369 merged2378 := by decide +kernel

theorem mergedZero2379 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2379 x = 0 := by
  rw [mergeCheck2379, Integer.Sparse.eval_merge]
  rw [mergedZero2369 x h, mergedZero2378 x h]
  simp only [add_zero]

theorem mergeCheck2380 : merged2380 = Integer.Sparse.merge merged2361 merged2379 := by decide +kernel

theorem mergedZero2380 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2380 x = 0 := by
  rw [mergeCheck2380, Integer.Sparse.eval_merge]
  rw [mergedZero2361 x h, mergedZero2379 x h]
  simp only [add_zero]

theorem mergeCheck2381 : merged2381 = Integer.Sparse.merge (Integer.Sparse.scale (-30816288000000) (sourceRows 2387)) (Integer.Sparse.scale (6163257600000) (sourceRows 2388)) := by decide +kernel

theorem mergedZero2381 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2381 x = 0 := by
  rw [mergeCheck2381, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2382 : merged2382 = Integer.Sparse.merge (Integer.Sparse.scale (7818206400000) (sourceRows 2389)) (Integer.Sparse.scale (-16435353600000) (sourceRows 2390)) := by decide +kernel

theorem mergedZero2382 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2382 x = 0 := by
  rw [mergeCheck2382, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2383 : merged2383 = Integer.Sparse.merge merged2381 merged2382 := by decide +kernel

theorem mergedZero2383 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2383 x = 0 := by
  rw [mergeCheck2383, Integer.Sparse.eval_merge]
  rw [mergedZero2381 x h, mergedZero2382 x h]
  simp only [add_zero]

theorem mergeCheck2384 : merged2384 = Integer.Sparse.merge (Integer.Sparse.scale (19688184000000) (sourceRows 2391)) (Integer.Sparse.scale (3287070720000) (sourceRows 2392)) := by decide +kernel

theorem mergedZero2384 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2384 x = 0 := by
  rw [mergeCheck2384, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2385 : merged2385 = Integer.Sparse.merge (Integer.Sparse.scale (-8217676800000) (sourceRows 2394)) (Integer.Sparse.scale (228725337600000) (sourceRows 2395)) := by decide +kernel

theorem mergedZero2385 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2385 x = 0 := by
  rw [mergeCheck2385, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2386 : merged2386 = Integer.Sparse.merge (Integer.Sparse.scale (-19996346880000) (sourceRows 2393)) merged2385 := by decide +kernel

theorem mergedZero2386 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2386 x = 0 := by
  rw [mergeCheck2386, Integer.Sparse.eval_merge]
  rw [mergedZero2385 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2387 : merged2387 = Integer.Sparse.merge merged2384 merged2386 := by decide +kernel

theorem mergedZero2387 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2387 x = 0 := by
  rw [mergeCheck2387, Integer.Sparse.eval_merge]
  rw [mergedZero2384 x h, mergedZero2386 x h]
  simp only [add_zero]

theorem mergeCheck2388 : merged2388 = Integer.Sparse.merge merged2383 merged2387 := by decide +kernel

theorem mergedZero2388 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2388 x = 0 := by
  rw [mergeCheck2388, Integer.Sparse.eval_merge]
  rw [mergedZero2383 x h, mergedZero2387 x h]
  simp only [add_zero]

theorem mergeCheck2389 : merged2389 = Integer.Sparse.merge (Integer.Sparse.scale (-19722424320000) (sourceRows 2396)) (Integer.Sparse.scale (-12098246400000) (sourceRows 2397)) := by decide +kernel

theorem mergedZero2389 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2389 x = 0 := by
  rw [mergeCheck2389, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2390 : merged2390 = Integer.Sparse.merge (Integer.Sparse.scale (6163257600000) (sourceRows 2399)) (Integer.Sparse.scale (-83888784000000) (sourceRows 2400)) := by decide +kernel

theorem mergedZero2390 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2390 x = 0 := by
  rw [mergeCheck2390, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2391 : merged2391 = Integer.Sparse.merge (Integer.Sparse.scale (5136048000000) (sourceRows 2398)) merged2390 := by decide +kernel

theorem mergedZero2391 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2391 x = 0 := by
  rw [mergeCheck2391, Integer.Sparse.eval_merge]
  rw [mergedZero2390 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2392 : merged2392 = Integer.Sparse.merge merged2389 merged2391 := by decide +kernel

theorem mergedZero2392 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2392 x = 0 := by
  rw [mergeCheck2392, Integer.Sparse.eval_merge]
  rw [mergedZero2389 x h, mergedZero2391 x h]
  simp only [add_zero]

theorem mergeCheck2393 : merged2393 = Integer.Sparse.merge (Integer.Sparse.scale (22598611200000) (sourceRows 2401)) (Integer.Sparse.scale (-8217676800000) (sourceRows 2402)) := by decide +kernel

theorem mergedZero2393 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2393 x = 0 := by
  rw [mergeCheck2393, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2394 : merged2394 = Integer.Sparse.merge (Integer.Sparse.scale (23968224000000) (sourceRows 2404)) (Integer.Sparse.scale (2054419200000) (sourceRows 2405)) := by decide +kernel

theorem mergedZero2394 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2394 x = 0 := by
  rw [mergeCheck2394, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2395 : merged2395 = Integer.Sparse.merge (Integer.Sparse.scale (-24379107840000) (sourceRows 2403)) merged2394 := by decide +kernel

theorem mergedZero2395 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2395 x = 0 := by
  rw [mergeCheck2395, Integer.Sparse.eval_merge]
  rw [mergedZero2394 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2396 : merged2396 = Integer.Sparse.merge merged2393 merged2395 := by decide +kernel

theorem mergedZero2396 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2396 x = 0 := by
  rw [mergeCheck2396, Integer.Sparse.eval_merge]
  rw [mergedZero2393 x h, mergedZero2395 x h]
  simp only [add_zero]

theorem mergeCheck2397 : merged2397 = Integer.Sparse.merge merged2392 merged2396 := by decide +kernel

theorem mergedZero2397 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2397 x = 0 := by
  rw [mergeCheck2397, Integer.Sparse.eval_merge]
  rw [mergedZero2392 x h, mergedZero2396 x h]
  simp only [add_zero]

theorem mergeCheck2398 : merged2398 = Integer.Sparse.merge merged2388 merged2397 := by decide +kernel

theorem mergedZero2398 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2398 x = 0 := by
  rw [mergeCheck2398, Integer.Sparse.eval_merge]
  rw [mergedZero2388 x h, mergedZero2397 x h]
  simp only [add_zero]

theorem mergeCheck2399 : merged2399 = Integer.Sparse.merge (Integer.Sparse.scale (-239682240000000) (sourceRows 2406)) (Integer.Sparse.scale (-160244697600000) (sourceRows 2407)) := by decide +kernel

theorem mergedZero2399 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2399 x = 0 := by
  rw [mergeCheck2399, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

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

theorem mergeCheck2400 : merged2400 = Integer.Sparse.merge (Integer.Sparse.scale (1232651520000) (sourceRows 2408)) (Integer.Sparse.scale (-10272096000000) (sourceRows 2409)) := by decide +kernel

theorem mergedZero2400 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2400 x = 0 := by
  rw [mergeCheck2400, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2401 : merged2401 = Integer.Sparse.merge merged2399 merged2400 := by decide +kernel

theorem mergedZero2401 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2401 x = 0 := by
  rw [mergeCheck2401, Integer.Sparse.eval_merge]
  rw [mergedZero2399 x h, mergedZero2400 x h]
  simp only [add_zero]

theorem mergeCheck2402 : merged2402 = Integer.Sparse.merge (Integer.Sparse.scale (-41088384000000) (sourceRows 2410)) (Integer.Sparse.scale (3492512640000) (sourceRows 2411)) := by decide +kernel

theorem mergedZero2402 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2402 x = 0 := by
  rw [mergeCheck2402, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2403 : merged2403 = Integer.Sparse.merge (Integer.Sparse.scale (-2465303040000) (sourceRows 2413)) (Integer.Sparse.scale (-3492512640000) (sourceRows 2414)) := by decide +kernel

theorem mergedZero2403 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2403 x = 0 := by
  rw [mergeCheck2403, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2404 : merged2404 = Integer.Sparse.merge (Integer.Sparse.scale (1438093440000) (sourceRows 2412)) merged2403 := by decide +kernel

theorem mergedZero2404 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2404 x = 0 := by
  rw [mergeCheck2404, Integer.Sparse.eval_merge]
  rw [mergedZero2403 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2405 : merged2405 = Integer.Sparse.merge merged2402 merged2404 := by decide +kernel

theorem mergedZero2405 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2405 x = 0 := by
  rw [mergeCheck2405, Integer.Sparse.eval_merge]
  rw [mergedZero2402 x h, mergedZero2404 x h]
  simp only [add_zero]

theorem mergeCheck2406 : merged2406 = Integer.Sparse.merge merged2401 merged2405 := by decide +kernel

theorem mergedZero2406 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2406 x = 0 := by
  rw [mergeCheck2406, Integer.Sparse.eval_merge]
  rw [mergedZero2401 x h, mergedZero2405 x h]
  simp only [add_zero]

theorem mergeCheck2407 : merged2407 = Integer.Sparse.merge (Integer.Sparse.scale (-1232651520000) (sourceRows 2415)) (Integer.Sparse.scale (-17257121280000) (sourceRows 2416)) := by decide +kernel

theorem mergedZero2407 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2407 x = 0 := by
  rw [mergeCheck2407, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2408 : merged2408 = Integer.Sparse.merge (Integer.Sparse.scale (12326515200000) (sourceRows 2418)) (Integer.Sparse.scale (-8217676800000) (sourceRows 2419)) := by decide +kernel

theorem mergedZero2408 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2408 x = 0 := by
  rw [mergeCheck2408, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2409 : merged2409 = Integer.Sparse.merge (Integer.Sparse.scale (9039444480000) (sourceRows 2417)) merged2408 := by decide +kernel

theorem mergedZero2409 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2409 x = 0 := by
  rw [mergeCheck2409, Integer.Sparse.eval_merge]
  rw [mergedZero2408 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2410 : merged2410 = Integer.Sparse.merge merged2407 merged2409 := by decide +kernel

theorem mergedZero2410 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2410 x = 0 := by
  rw [mergeCheck2410, Integer.Sparse.eval_merge]
  rw [mergedZero2407 x h, mergedZero2409 x h]
  simp only [add_zero]

theorem mergeCheck2411 : merged2411 = Integer.Sparse.merge (Integer.Sparse.scale (2465303040000) (sourceRows 2420)) (Integer.Sparse.scale (8217676800000) (sourceRows 2421)) := by decide +kernel

theorem mergedZero2411 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2411 x = 0 := by
  rw [mergeCheck2411, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2412 : merged2412 = Integer.Sparse.merge (Integer.Sparse.scale (20544192000000) (sourceRows 2423)) (Integer.Sparse.scale (8217676800000) (sourceRows 2424)) := by decide +kernel

theorem mergedZero2412 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2412 x = 0 := by
  rw [mergeCheck2412, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2413 : merged2413 = Integer.Sparse.merge (Integer.Sparse.scale (-9039444480000) (sourceRows 2422)) merged2412 := by decide +kernel

theorem mergedZero2413 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2413 x = 0 := by
  rw [mergeCheck2413, Integer.Sparse.eval_merge]
  rw [mergedZero2412 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck2414 : merged2414 = Integer.Sparse.merge merged2411 merged2413 := by decide +kernel

theorem mergedZero2414 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2414 x = 0 := by
  rw [mergeCheck2414, Integer.Sparse.eval_merge]
  rw [mergedZero2411 x h, mergedZero2413 x h]
  simp only [add_zero]

theorem mergeCheck2415 : merged2415 = Integer.Sparse.merge merged2410 merged2414 := by decide +kernel

theorem mergedZero2415 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2415 x = 0 := by
  rw [mergeCheck2415, Integer.Sparse.eval_merge]
  rw [mergedZero2410 x h, mergedZero2414 x h]
  simp only [add_zero]

theorem mergeCheck2416 : merged2416 = Integer.Sparse.merge merged2406 merged2415 := by decide +kernel

theorem mergedZero2416 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2416 x = 0 := by
  rw [mergeCheck2416, Integer.Sparse.eval_merge]
  rw [mergedZero2406 x h, mergedZero2415 x h]
  simp only [add_zero]

theorem mergeCheck2417 : merged2417 = Integer.Sparse.merge merged2398 merged2416 := by decide +kernel

theorem mergedZero2417 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2417 x = 0 := by
  rw [mergeCheck2417, Integer.Sparse.eval_merge]
  rw [mergedZero2398 x h, mergedZero2416 x h]
  simp only [add_zero]

theorem mergeCheck2418 : merged2418 = Integer.Sparse.merge merged2380 merged2417 := by decide +kernel

theorem mergedZero2418 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2418 x = 0 := by
  rw [mergeCheck2418, Integer.Sparse.eval_merge]
  rw [mergedZero2380 x h, mergedZero2417 x h]
  simp only [add_zero]

theorem mergeCheck2419 : merged2419 = Integer.Sparse.merge merged2343 merged2418 := by decide +kernel

theorem mergedZero2419_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged2419 x = 0 := by
  rw [mergeCheck2419, Integer.Sparse.eval_merge]
  rw [mergedZero2343 x h, mergedZero2418 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero2419_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero2419_e_oai
