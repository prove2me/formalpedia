-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero1511_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:22:15.980137+00:00
-- url     : https://prove2.me/submissions/6d54dea8-7c35-4d8d-a44e-e7b40a6bf1ec

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E180
import Definitions.Def_OAIQ106E059
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1361 : merged1361 = Integer.Sparse.merge (Integer.Sparse.scale (-23071087813917465907200) (sourceRows 1363)) (Integer.Sparse.scale (165755627813353732761600) (sourceRows 1364)) := by decide +kernel

theorem mergedZero1361 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1361 x = 0 := by
  rw [mergeCheck1361, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1362 : merged1362 = Integer.Sparse.merge (Integer.Sparse.scale (-431411357807816601600) (sourceRows 1365)) (Integer.Sparse.scale (-3192793390311224716800) (sourceRows 1366)) := by decide +kernel

theorem mergedZero1362 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1362 x = 0 := by
  rw [mergeCheck1362, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1363 : merged1363 = Integer.Sparse.merge merged1361 merged1362 := by decide +kernel

theorem mergedZero1363 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1363 x = 0 := by
  rw [mergeCheck1363, Integer.Sparse.eval_merge]
  rw [mergedZero1361 x h, mergedZero1362 x h]
  simp only [add_zero]

theorem mergeCheck1364 : merged1364 = Integer.Sparse.merge (Integer.Sparse.scale (64677926889532299571200) (sourceRows 1367)) (Integer.Sparse.scale (8866342106431488000000) (sourceRows 1368)) := by decide +kernel

theorem mergedZero1364 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1364 x = 0 := by
  rw [mergeCheck1364, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1365 : merged1365 = Integer.Sparse.merge (Integer.Sparse.scale (-68163802177680418003200) (sourceRows 1370)) (Integer.Sparse.scale (429263611252241472000) (sourceRows 1371)) := by decide +kernel

theorem mergedZero1365 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1365 x = 0 := by
  rw [mergeCheck1365, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1366 : merged1366 = Integer.Sparse.merge (Integer.Sparse.scale (143251566798064435200) (sourceRows 1369)) merged1365 := by decide +kernel

theorem mergedZero1366 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1366 x = 0 := by
  rw [mergeCheck1366, Integer.Sparse.eval_merge]
  rw [mergedZero1365 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1367 : merged1367 = Integer.Sparse.merge merged1364 merged1366 := by decide +kernel

theorem mergedZero1367 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1367 x = 0 := by
  rw [mergeCheck1367, Integer.Sparse.eval_merge]
  rw [mergedZero1364 x h, mergedZero1366 x h]
  simp only [add_zero]

theorem mergeCheck1368 : merged1368 = Integer.Sparse.merge merged1363 merged1367 := by decide +kernel

theorem mergedZero1368 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1368 x = 0 := by
  rw [mergeCheck1368, Integer.Sparse.eval_merge]
  rw [mergedZero1363 x h, mergedZero1367 x h]
  simp only [add_zero]

theorem mergeCheck1369 : merged1369 = Integer.Sparse.merge (Integer.Sparse.scale (-152710294346763148800) (sourceRows 1372)) (Integer.Sparse.scale (129872229830815926988800) (sourceRows 1373)) := by decide +kernel

theorem mergedZero1369 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1369 x = 0 := by
  rw [mergeCheck1369, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1370 : merged1370 = Integer.Sparse.merge (Integer.Sparse.scale (-67766760616439769292800) (sourceRows 1375)) (Integer.Sparse.scale (320876977053946470796800) (sourceRows 1376)) := by decide +kernel

theorem mergedZero1370 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1370 x = 0 := by
  rw [mergeCheck1370, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1371 : merged1371 = Integer.Sparse.merge (Integer.Sparse.scale (-51373781924880373862400) (sourceRows 1374)) merged1370 := by decide +kernel

theorem mergedZero1371 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1371 x = 0 := by
  rw [mergeCheck1371, Integer.Sparse.eval_merge]
  rw [mergedZero1370 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1372 : merged1372 = Integer.Sparse.merge merged1369 merged1371 := by decide +kernel

theorem mergedZero1372 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1372 x = 0 := by
  rw [mergeCheck1372, Integer.Sparse.eval_merge]
  rw [mergedZero1369 x h, mergedZero1371 x h]
  simp only [add_zero]

theorem mergeCheck1373 : merged1373 = Integer.Sparse.merge (Integer.Sparse.scale (-160869415546389080160000) (sourceRows 1377)) (Integer.Sparse.scale (-862790004876802867200) (sourceRows 1378)) := by decide +kernel

theorem mergedZero1373 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1373 x = 0 := by
  rw [mergeCheck1373, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1374 : merged1374 = Integer.Sparse.merge (Integer.Sparse.scale (437196496046990400000) (sourceRows 1380)) (Integer.Sparse.scale (861930379215269683200) (sourceRows 1381)) := by decide +kernel

theorem mergedZero1374 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1374 x = 0 := by
  rw [mergeCheck1374, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1375 : merged1375 = Integer.Sparse.merge (Integer.Sparse.scale (345623172524513787859200) (sourceRows 1379)) merged1374 := by decide +kernel

theorem mergedZero1375 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1375 x = 0 := by
  rw [mergeCheck1375, Integer.Sparse.eval_merge]
  rw [mergedZero1374 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1376 : merged1376 = Integer.Sparse.merge merged1373 merged1375 := by decide +kernel

theorem mergedZero1376 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1376 x = 0 := by
  rw [mergeCheck1376, Integer.Sparse.eval_merge]
  rw [mergedZero1373 x h, mergedZero1375 x h]
  simp only [add_zero]

theorem mergeCheck1377 : merged1377 = Integer.Sparse.merge merged1372 merged1376 := by decide +kernel

theorem mergedZero1377 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1377 x = 0 := by
  rw [mergeCheck1377, Integer.Sparse.eval_merge]
  rw [mergedZero1372 x h, mergedZero1376 x h]
  simp only [add_zero]

theorem mergeCheck1378 : merged1378 = Integer.Sparse.merge merged1368 merged1377 := by decide +kernel

theorem mergedZero1378 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1378 x = 0 := by
  rw [mergeCheck1378, Integer.Sparse.eval_merge]
  rw [mergedZero1368 x h, mergedZero1377 x h]
  simp only [add_zero]

theorem mergeCheck1379 : merged1379 = Integer.Sparse.merge (Integer.Sparse.scale (-17921366125916198400) (sourceRows 1382)) (Integer.Sparse.scale (-135836451883032922828800) (sourceRows 1383)) := by decide +kernel

theorem mergedZero1379 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1379 x = 0 := by
  rw [mergeCheck1379, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1380 : merged1380 = Integer.Sparse.merge (Integer.Sparse.scale (-171326753859610524672000) (sourceRows 1384)) (Integer.Sparse.scale (-136676309413056382771200) (sourceRows 1385)) := by decide +kernel

theorem mergedZero1380 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1380 x = 0 := by
  rw [mergeCheck1380, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1381 : merged1381 = Integer.Sparse.merge merged1379 merged1380 := by decide +kernel

theorem mergedZero1381 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1381 x = 0 := by
  rw [mergeCheck1381, Integer.Sparse.eval_merge]
  rw [mergedZero1379 x h, mergedZero1380 x h]
  simp only [add_zero]

theorem mergeCheck1382 : merged1382 = Integer.Sparse.merge (Integer.Sparse.scale (-320015614946861567462400) (sourceRows 1386)) (Integer.Sparse.scale (113770359674186699131200) (sourceRows 1387)) := by decide +kernel

theorem mergedZero1382 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1382 x = 0 := by
  rw [mergeCheck1382, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1383 : merged1383 = Integer.Sparse.merge (Integer.Sparse.scale (11229056997704663040000) (sourceRows 1389)) (Integer.Sparse.scale (-89471928420058512384000) (sourceRows 1390)) := by decide +kernel

theorem mergedZero1383 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1383 x = 0 := by
  rw [mergeCheck1383, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1384 : merged1384 = Integer.Sparse.merge (Integer.Sparse.scale (207124311996370584950400) (sourceRows 1388)) merged1383 := by decide +kernel

theorem mergedZero1384 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1384 x = 0 := by
  rw [mergeCheck1384, Integer.Sparse.eval_merge]
  rw [mergedZero1383 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1385 : merged1385 = Integer.Sparse.merge merged1382 merged1384 := by decide +kernel

theorem mergedZero1385 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1385 x = 0 := by
  rw [mergeCheck1385, Integer.Sparse.eval_merge]
  rw [mergedZero1382 x h, mergedZero1384 x h]
  simp only [add_zero]

theorem mergeCheck1386 : merged1386 = Integer.Sparse.merge merged1381 merged1385 := by decide +kernel

theorem mergedZero1386 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1386 x = 0 := by
  rw [mergeCheck1386, Integer.Sparse.eval_merge]
  rw [mergedZero1381 x h, mergedZero1385 x h]
  simp only [add_zero]

theorem mergeCheck1387 : merged1387 = Integer.Sparse.merge (Integer.Sparse.scale (28451683432081573171200) (sourceRows 1391)) (Integer.Sparse.scale (-46157893582287068467200) (sourceRows 1392)) := by decide +kernel

theorem mergedZero1387 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1387 x = 0 := by
  rw [mergeCheck1387, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1388 : merged1388 = Integer.Sparse.merge (Integer.Sparse.scale (-68398265196126762220800) (sourceRows 1394)) (Integer.Sparse.scale (416283952201063833600) (sourceRows 1395)) := by decide +kernel

theorem mergedZero1388 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1388 x = 0 := by
  rw [mergeCheck1388, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1389 : merged1389 = Integer.Sparse.merge (Integer.Sparse.scale (146606325458367398400) (sourceRows 1393)) merged1388 := by decide +kernel

theorem mergedZero1389 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1389 x = 0 := by
  rw [mergeCheck1389, Integer.Sparse.eval_merge]
  rw [mergedZero1388 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1390 : merged1390 = Integer.Sparse.merge merged1387 merged1389 := by decide +kernel

theorem mergedZero1390 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1390 x = 0 := by
  rw [mergeCheck1390, Integer.Sparse.eval_merge]
  rw [mergedZero1387 x h, mergedZero1389 x h]
  simp only [add_zero]

theorem mergeCheck1391 : merged1391 = Integer.Sparse.merge (Integer.Sparse.scale (-432425318832576921600) (sourceRows 1396)) (Integer.Sparse.scale (51570885219353237606400) (sourceRows 1397)) := by decide +kernel

theorem mergedZero1391 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1391 x = 0 := by
  rw [mergeCheck1391, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1392 : merged1392 = Integer.Sparse.merge (Integer.Sparse.scale (-67744997976789370944000) (sourceRows 1399)) (Integer.Sparse.scale (-12806871250749811200) (sourceRows 1400)) := by decide +kernel

theorem mergedZero1392 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1392 x = 0 := by
  rw [mergeCheck1392, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1393 : merged1393 = Integer.Sparse.merge (Integer.Sparse.scale (32576434950722535936000) (sourceRows 1398)) merged1392 := by decide +kernel

theorem mergedZero1393 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1393 x = 0 := by
  rw [mergeCheck1393, Integer.Sparse.eval_merge]
  rw [mergedZero1392 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1394 : merged1394 = Integer.Sparse.merge merged1391 merged1393 := by decide +kernel

theorem mergedZero1394 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1394 x = 0 := by
  rw [mergeCheck1394, Integer.Sparse.eval_merge]
  rw [mergedZero1391 x h, mergedZero1393 x h]
  simp only [add_zero]

theorem mergeCheck1395 : merged1395 = Integer.Sparse.merge merged1390 merged1394 := by decide +kernel

theorem mergedZero1395 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1395 x = 0 := by
  rw [mergeCheck1395, Integer.Sparse.eval_merge]
  rw [mergedZero1390 x h, mergedZero1394 x h]
  simp only [add_zero]

theorem mergeCheck1396 : merged1396 = Integer.Sparse.merge merged1386 merged1395 := by decide +kernel

theorem mergedZero1396 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1396 x = 0 := by
  rw [mergeCheck1396, Integer.Sparse.eval_merge]
  rw [mergedZero1386 x h, mergedZero1395 x h]
  simp only [add_zero]

theorem mergeCheck1397 : merged1397 = Integer.Sparse.merge merged1378 merged1396 := by decide +kernel

theorem mergedZero1397 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1397 x = 0 := by
  rw [mergeCheck1397, Integer.Sparse.eval_merge]
  rw [mergedZero1378 x h, mergedZero1396 x h]
  simp only [add_zero]

theorem mergeCheck1398 : merged1398 = Integer.Sparse.merge (Integer.Sparse.scale (-6008535238307212800) (sourceRows 1401)) (Integer.Sparse.scale (802790865968716800) (sourceRows 1402)) := by decide +kernel

theorem mergedZero1398 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1398 x = 0 := by
  rw [mergeCheck1398, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1399 : merged1399 = Integer.Sparse.merge (Integer.Sparse.scale (-2810315888578598400) (sourceRows 1403)) (Integer.Sparse.scale (-159864441913140327417600) (sourceRows 1404)) := by decide +kernel

theorem mergedZero1399 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1399 x = 0 := by
  rw [mergeCheck1399, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1400 : merged1400 = Integer.Sparse.merge merged1398 merged1399 := by decide +kernel

theorem mergedZero1400 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1400 x = 0 := by
  rw [mergeCheck1400, Integer.Sparse.eval_merge]
  rw [mergedZero1398 x h, mergedZero1399 x h]
  simp only [add_zero]

theorem mergeCheck1401 : merged1401 = Integer.Sparse.merge (Integer.Sparse.scale (430965189607634841600) (sourceRows 1405)) (Integer.Sparse.scale (160581740093771299833600) (sourceRows 1406)) := by decide +kernel

theorem mergedZero1401 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1401 x = 0 := by
  rw [mergeCheck1401, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1402 : merged1402 = Integer.Sparse.merge (Integer.Sparse.scale (-7695955372738348800) (sourceRows 1408)) (Integer.Sparse.scale (251216689248000) (sourceRows 1409)) := by decide +kernel

theorem mergedZero1402 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1402 x = 0 := by
  rw [mergeCheck1402, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1403 : merged1403 = Integer.Sparse.merge (Integer.Sparse.scale (430965189607634841600) (sourceRows 1407)) merged1402 := by decide +kernel

theorem mergedZero1403 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1403 x = 0 := by
  rw [mergeCheck1403, Integer.Sparse.eval_merge]
  rw [mergedZero1402 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1404 : merged1404 = Integer.Sparse.merge merged1401 merged1403 := by decide +kernel

theorem mergedZero1404 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1404 x = 0 := by
  rw [mergeCheck1404, Integer.Sparse.eval_merge]
  rw [mergedZero1401 x h, mergedZero1403 x h]
  simp only [add_zero]

theorem mergeCheck1405 : merged1405 = Integer.Sparse.merge merged1400 merged1404 := by decide +kernel

theorem mergedZero1405 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1405 x = 0 := by
  rw [mergeCheck1405, Integer.Sparse.eval_merge]
  rw [mergedZero1400 x h, mergedZero1404 x h]
  simp only [add_zero]

theorem mergeCheck1406 : merged1406 = Integer.Sparse.merge (Integer.Sparse.scale (512663350878604800) (sourceRows 1410)) (Integer.Sparse.scale (4573335150720000) (sourceRows 1411)) := by decide +kernel

theorem mergedZero1406 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1406 x = 0 := by
  rw [mergeCheck1406, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1407 : merged1407 = Integer.Sparse.merge (Integer.Sparse.scale (-24915166617600) (sourceRows 1413)) (Integer.Sparse.scale (-21204588916134328320) (sourceRows 1414)) := by decide +kernel

theorem mergedZero1407 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1407 x = 0 := by
  rw [mergeCheck1407, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1408 : merged1408 = Integer.Sparse.merge (Integer.Sparse.scale (170202771849146400000) (sourceRows 1412)) merged1407 := by decide +kernel

theorem mergedZero1408 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1408 x = 0 := by
  rw [mergeCheck1408, Integer.Sparse.eval_merge]
  rw [mergedZero1407 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1409 : merged1409 = Integer.Sparse.merge merged1406 merged1408 := by decide +kernel

theorem mergedZero1409 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1409 x = 0 := by
  rw [mergeCheck1409, Integer.Sparse.eval_merge]
  rw [mergedZero1406 x h, mergedZero1408 x h]
  simp only [add_zero]

theorem mergeCheck1410 : merged1410 = Integer.Sparse.merge (Integer.Sparse.scale (-160292011453262132472000) (sourceRows 1415)) (Integer.Sparse.scale (192112078568775321600) (sourceRows 1416)) := by decide +kernel

theorem mergedZero1410 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1410 x = 0 := by
  rw [mergeCheck1410, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1411 : merged1411 = Integer.Sparse.merge (Integer.Sparse.scale (15661245129057803520) (sourceRows 1418)) (Integer.Sparse.scale (9279509299200) (sourceRows 1419)) := by decide +kernel

theorem mergedZero1411 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1411 x = 0 := by
  rw [mergeCheck1411, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1412 : merged1412 = Integer.Sparse.merge (Integer.Sparse.scale (2172272785804800) (sourceRows 1417)) merged1411 := by decide +kernel

theorem mergedZero1412 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1412 x = 0 := by
  rw [mergeCheck1412, Integer.Sparse.eval_merge]
  rw [mergedZero1411 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1413 : merged1413 = Integer.Sparse.merge merged1410 merged1412 := by decide +kernel

theorem mergedZero1413 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1413 x = 0 := by
  rw [mergeCheck1413, Integer.Sparse.eval_merge]
  rw [mergedZero1410 x h, mergedZero1412 x h]
  simp only [add_zero]

theorem mergeCheck1414 : merged1414 = Integer.Sparse.merge merged1409 merged1413 := by decide +kernel

theorem mergedZero1414 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1414 x = 0 := by
  rw [mergeCheck1414, Integer.Sparse.eval_merge]
  rw [mergedZero1409 x h, mergedZero1413 x h]
  simp only [add_zero]

theorem mergeCheck1415 : merged1415 = Integer.Sparse.merge merged1405 merged1414 := by decide +kernel

theorem mergedZero1415 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1415 x = 0 := by
  rw [mergeCheck1415, Integer.Sparse.eval_merge]
  rw [mergedZero1405 x h, mergedZero1414 x h]
  simp only [add_zero]

theorem mergeCheck1416 : merged1416 = Integer.Sparse.merge (Integer.Sparse.scale (-118320732633600) (sourceRows 1420)) (Integer.Sparse.scale (64658553523200) (sourceRows 1421)) := by decide +kernel

theorem mergedZero1416 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1416 x = 0 := by
  rw [mergeCheck1416, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1417 : merged1417 = Integer.Sparse.merge (Integer.Sparse.scale (5531015292122234880000) (sourceRows 1422)) (Integer.Sparse.scale (-5291015869217917440) (sourceRows 1423)) := by decide +kernel

theorem mergedZero1417 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1417 x = 0 := by
  rw [mergeCheck1417, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1418 : merged1418 = Integer.Sparse.merge merged1416 merged1417 := by decide +kernel

theorem mergedZero1418 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1418 x = 0 := by
  rw [mergeCheck1418, Integer.Sparse.eval_merge]
  rw [mergedZero1416 x h, mergedZero1417 x h]
  simp only [add_zero]

theorem mergeCheck1419 : merged1419 = Integer.Sparse.merge (Integer.Sparse.scale (5531269217747116032000) (sourceRows 1424)) (Integer.Sparse.scale (44175725181687988224000) (sourceRows 1425)) := by decide +kernel

theorem mergedZero1419 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1419 x = 0 := by
  rw [mergeCheck1419, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1420 : merged1420 = Integer.Sparse.merge (Integer.Sparse.scale (-22718056872799411200) (sourceRows 1427)) (Integer.Sparse.scale (-13096731972561076224000) (sourceRows 1428)) := by decide +kernel

theorem mergedZero1420 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1420 x = 0 := by
  rw [mergeCheck1420, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1421 : merged1421 = Integer.Sparse.merge (Integer.Sparse.scale (10819766500584652800) (sourceRows 1426)) merged1420 := by decide +kernel

theorem mergedZero1421 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1421 x = 0 := by
  rw [mergeCheck1421, Integer.Sparse.eval_merge]
  rw [mergedZero1420 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1422 : merged1422 = Integer.Sparse.merge merged1419 merged1421 := by decide +kernel

theorem mergedZero1422 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1422 x = 0 := by
  rw [mergeCheck1422, Integer.Sparse.eval_merge]
  rw [mergedZero1419 x h, mergedZero1421 x h]
  simp only [add_zero]

theorem mergeCheck1423 : merged1423 = Integer.Sparse.merge merged1418 merged1422 := by decide +kernel

theorem mergedZero1423 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1423 x = 0 := by
  rw [mergeCheck1423, Integer.Sparse.eval_merge]
  rw [mergedZero1418 x h, mergedZero1422 x h]
  simp only [add_zero]

theorem mergeCheck1424 : merged1424 = Integer.Sparse.merge (Integer.Sparse.scale (-25991232319595410560) (sourceRows 1429)) (Integer.Sparse.scale (-13098254188955314176000) (sourceRows 1430)) := by decide +kernel

theorem mergedZero1424 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1424 x = 0 := by
  rw [mergeCheck1424, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1425 : merged1425 = Integer.Sparse.merge (Integer.Sparse.scale (112310217795575681280000) (sourceRows 1432)) (Integer.Sparse.scale (-39440244211200) (sourceRows 1433)) := by decide +kernel

theorem mergedZero1425 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1425 x = 0 := by
  rw [mergeCheck1425, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1426 : merged1426 = Integer.Sparse.merge (Integer.Sparse.scale (-49921826970737114265600) (sourceRows 1431)) merged1425 := by decide +kernel

theorem mergedZero1426 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1426 x = 0 := by
  rw [mergeCheck1426, Integer.Sparse.eval_merge]
  rw [mergedZero1425 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1427 : merged1427 = Integer.Sparse.merge merged1424 merged1426 := by decide +kernel

theorem mergedZero1427 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1427 x = 0 := by
  rw [mergeCheck1427, Integer.Sparse.eval_merge]
  rw [mergedZero1424 x h, mergedZero1426 x h]
  simp only [add_zero]

theorem mergeCheck1428 : merged1428 = Integer.Sparse.merge (Integer.Sparse.scale (-222419530368000) (sourceRows 1434)) (Integer.Sparse.scale (-271068188428800) (sourceRows 1435)) := by decide +kernel

theorem mergedZero1428 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1428 x = 0 := by
  rw [mergeCheck1428, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1429 : merged1429 = Integer.Sparse.merge (Integer.Sparse.scale (8315514121682053440) (sourceRows 1437)) (Integer.Sparse.scale (-1911830744916836352000) (sourceRows 1438)) := by decide +kernel

theorem mergedZero1429 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1429 x = 0 := by
  rw [mergeCheck1429, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1430 : merged1430 = Integer.Sparse.merge (Integer.Sparse.scale (-1911455718309494784000) (sourceRows 1436)) merged1429 := by decide +kernel

theorem mergedZero1430 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1430 x = 0 := by
  rw [mergeCheck1430, Integer.Sparse.eval_merge]
  rw [mergedZero1429 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1431 : merged1431 = Integer.Sparse.merge merged1428 merged1430 := by decide +kernel

theorem mergedZero1431 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1431 x = 0 := by
  rw [mergeCheck1431, Integer.Sparse.eval_merge]
  rw [mergedZero1428 x h, mergedZero1430 x h]
  simp only [add_zero]

theorem mergeCheck1432 : merged1432 = Integer.Sparse.merge merged1427 merged1431 := by decide +kernel

theorem mergedZero1432 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1432 x = 0 := by
  rw [mergeCheck1432, Integer.Sparse.eval_merge]
  rw [mergedZero1427 x h, mergedZero1431 x h]
  simp only [add_zero]

theorem mergeCheck1433 : merged1433 = Integer.Sparse.merge merged1423 merged1432 := by decide +kernel

theorem mergedZero1433 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1433 x = 0 := by
  rw [mergeCheck1433, Integer.Sparse.eval_merge]
  rw [mergedZero1423 x h, mergedZero1432 x h]
  simp only [add_zero]

theorem mergeCheck1434 : merged1434 = Integer.Sparse.merge merged1415 merged1433 := by decide +kernel

theorem mergedZero1434 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1434 x = 0 := by
  rw [mergeCheck1434, Integer.Sparse.eval_merge]
  rw [mergedZero1415 x h, mergedZero1433 x h]
  simp only [add_zero]

theorem mergeCheck1435 : merged1435 = Integer.Sparse.merge merged1397 merged1434 := by decide +kernel

theorem mergedZero1435 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1435 x = 0 := by
  rw [mergeCheck1435, Integer.Sparse.eval_merge]
  rw [mergedZero1397 x h, mergedZero1434 x h]
  simp only [add_zero]

theorem mergeCheck1436 : merged1436 = Integer.Sparse.merge (Integer.Sparse.scale (88213433689640254464000) (sourceRows 1439)) (Integer.Sparse.scale (32559319209646275379200) (sourceRows 1440)) := by decide +kernel

theorem mergedZero1436 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1436 x = 0 := by
  rw [mergeCheck1436, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1437 : merged1437 = Integer.Sparse.merge (Integer.Sparse.scale (-118320732633600) (sourceRows 1441)) (Integer.Sparse.scale (64658553523200) (sourceRows 1442)) := by decide +kernel

theorem mergedZero1437 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1437 x = 0 := by
  rw [mergeCheck1437, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1438 : merged1438 = Integer.Sparse.merge merged1436 merged1437 := by decide +kernel

theorem mergedZero1438 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1438 x = 0 := by
  rw [mergeCheck1438, Integer.Sparse.eval_merge]
  rw [mergedZero1436 x h, mergedZero1437 x h]
  simp only [add_zero]

theorem mergeCheck1439 : merged1439 = Integer.Sparse.merge (Integer.Sparse.scale (18423936167248281600) (sourceRows 1443)) (Integer.Sparse.scale (1171014574012416000) (sourceRows 1444)) := by decide +kernel

theorem mergedZero1439 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1439 x = 0 := by
  rw [mergeCheck1439, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1440 : merged1440 = Integer.Sparse.merge (Integer.Sparse.scale (-17921366125916198400) (sourceRows 1446)) (Integer.Sparse.scale (13706648206420377600) (sourceRows 1447)) := by decide +kernel

theorem mergedZero1440 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1440 x = 0 := by
  rw [mergeCheck1440, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1441 : merged1441 = Integer.Sparse.merge (Integer.Sparse.scale (-15391910745476697600) (sourceRows 1445)) merged1440 := by decide +kernel

theorem mergedZero1441 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1441 x = 0 := by
  rw [mergeCheck1441, Integer.Sparse.eval_merge]
  rw [mergedZero1440 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1442 : merged1442 = Integer.Sparse.merge merged1439 merged1441 := by decide +kernel

theorem mergedZero1442 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1442 x = 0 := by
  rw [mergeCheck1442, Integer.Sparse.eval_merge]
  rw [mergedZero1439 x h, mergedZero1441 x h]
  simp only [add_zero]

theorem mergeCheck1443 : merged1443 = Integer.Sparse.merge merged1438 merged1442 := by decide +kernel

theorem mergedZero1443 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1443 x = 0 := by
  rw [mergeCheck1443, Integer.Sparse.eval_merge]
  rw [mergedZero1438 x h, mergedZero1442 x h]
  simp only [add_zero]

theorem mergeCheck1444 : merged1444 = Integer.Sparse.merge (Integer.Sparse.scale (1171014574012416000) (sourceRows 1448)) (Integer.Sparse.scale (-13260950362186329600) (sourceRows 1449)) := by decide +kernel

theorem mergedZero1444 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1444 x = 0 := by
  rw [mergeCheck1444, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1445 : merged1445 = Integer.Sparse.merge (Integer.Sparse.scale (9211968083624140800) (sourceRows 1451)) (Integer.Sparse.scale (-143296883763399475200) (sourceRows 1452)) := by decide +kernel

theorem mergedZero1445 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1445 x = 0 := by
  rw [mergeCheck1445, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1446 : merged1446 = Integer.Sparse.merge (Integer.Sparse.scale (-6403435625374905600) (sourceRows 1450)) merged1445 := by decide +kernel

theorem mergedZero1446 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1446 x = 0 := by
  rw [mergeCheck1446, Integer.Sparse.eval_merge]
  rw [mergedZero1445 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1447 : merged1447 = Integer.Sparse.merge merged1444 merged1446 := by decide +kernel

theorem mergedZero1447 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1447 x = 0 := by
  rw [mergeCheck1447, Integer.Sparse.eval_merge]
  rw [mergedZero1444 x h, mergedZero1446 x h]
  simp only [add_zero]

theorem mergeCheck1448 : merged1448 = Integer.Sparse.merge (Integer.Sparse.scale (86098259942079402326400) (sourceRows 1453)) (Integer.Sparse.scale (-6367205157173449344000) (sourceRows 1454)) := by decide +kernel

theorem mergedZero1448 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1448 x = 0 := by
  rw [mergeCheck1448, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1449 : merged1449 = Integer.Sparse.merge (Integer.Sparse.scale (86100745964858126409600) (sourceRows 1456)) (Integer.Sparse.scale (-3182107494087132307200) (sourceRows 1457)) := by decide +kernel

theorem mergedZero1449 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1449 x = 0 := by
  rw [mergeCheck1449, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1450 : merged1450 = Integer.Sparse.merge (Integer.Sparse.scale (-139896808137761472000) (sourceRows 1455)) merged1449 := by decide +kernel

theorem mergedZero1450 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1450 x = 0 := by
  rw [mergeCheck1450, Integer.Sparse.eval_merge]
  rw [mergedZero1449 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1451 : merged1451 = Integer.Sparse.merge merged1448 merged1450 := by decide +kernel

theorem mergedZero1451 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1451 x = 0 := by
  rw [mergeCheck1451, Integer.Sparse.eval_merge]
  rw [mergedZero1448 x h, mergedZero1450 x h]
  simp only [add_zero]

theorem mergeCheck1452 : merged1452 = Integer.Sparse.merge merged1447 merged1451 := by decide +kernel

theorem mergedZero1452 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1452 x = 0 := by
  rw [mergeCheck1452, Integer.Sparse.eval_merge]
  rw [mergedZero1447 x h, mergedZero1451 x h]
  simp only [add_zero]

theorem mergeCheck1453 : merged1453 = Integer.Sparse.merge merged1443 merged1452 := by decide +kernel

theorem mergedZero1453 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1453 x = 0 := by
  rw [mergeCheck1453, Integer.Sparse.eval_merge]
  rw [mergedZero1443 x h, mergedZero1452 x h]
  simp only [add_zero]

theorem mergeCheck1454 : merged1454 = Integer.Sparse.merge (Integer.Sparse.scale (-92461137752991305491200) (sourceRows 1458)) (Integer.Sparse.scale (-143251566798064435200) (sourceRows 1459)) := by decide +kernel

theorem mergedZero1454 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1454 x = 0 := by
  rw [mergeCheck1454, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1455 : merged1455 = Integer.Sparse.merge (Integer.Sparse.scale (178555093605859195814400) (sourceRows 1460)) (Integer.Sparse.scale (86113400884459662268800) (sourceRows 1461)) := by decide +kernel

theorem mergedZero1455 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1455 x = 0 := by
  rw [mergeCheck1455, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1456 : merged1456 = Integer.Sparse.merge merged1454 merged1455 := by decide +kernel

theorem mergedZero1456 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1456 x = 0 := by
  rw [mergeCheck1456, Integer.Sparse.eval_merge]
  rw [mergedZero1454 x h, mergedZero1455 x h]
  simp only [add_zero]

theorem mergeCheck1457 : merged1457 = Integer.Sparse.merge (Integer.Sparse.scale (-184922275505982610982400) (sourceRows 1462)) (Integer.Sparse.scale (-286503133596128870400) (sourceRows 1463)) := by decide +kernel

theorem mergedZero1457 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1457 x = 0 := by
  rw [mergeCheck1457, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1458 : merged1458 = Integer.Sparse.merge (Integer.Sparse.scale (-3339015098258423808000) (sourceRows 1465)) (Integer.Sparse.scale (-3338968547674109952000) (sourceRows 1466)) := by decide +kernel

theorem mergedZero1458 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1458 x = 0 := by
  rw [mergeCheck1458, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1459 : merged1459 = Integer.Sparse.merge (Integer.Sparse.scale (209349022002880884364800) (sourceRows 1464)) merged1458 := by decide +kernel

theorem mergedZero1459 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1459 x = 0 := by
  rw [mergeCheck1459, Integer.Sparse.eval_merge]
  rw [mergedZero1458 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1460 : merged1460 = Integer.Sparse.merge merged1457 merged1459 := by decide +kernel

theorem mergedZero1460 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1460 x = 0 := by
  rw [mergeCheck1460, Integer.Sparse.eval_merge]
  rw [mergedZero1457 x h, mergedZero1459 x h]
  simp only [add_zero]

theorem mergeCheck1461 : merged1461 = Integer.Sparse.merge merged1456 merged1460 := by decide +kernel

theorem mergedZero1461 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1461 x = 0 := by
  rw [mergeCheck1461, Integer.Sparse.eval_merge]
  rw [mergedZero1456 x h, mergedZero1460 x h]
  simp only [add_zero]

theorem mergeCheck1462 : merged1462 = Integer.Sparse.merge (Integer.Sparse.scale (-13550058397951488000000) (sourceRows 1467)) (Integer.Sparse.scale (61621542834314958028800) (sourceRows 1468)) := by decide +kernel

theorem mergedZero1462 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1462 x = 0 := by
  rw [mergeCheck1462, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1463 : merged1463 = Integer.Sparse.merge (Integer.Sparse.scale (33160084906959360) (sourceRows 1470)) (Integer.Sparse.scale (15253689507414736896000) (sourceRows 1471)) := by decide +kernel

theorem mergedZero1463 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1463 x = 0 := by
  rw [mergeCheck1463, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1464 : merged1464 = Integer.Sparse.merge (Integer.Sparse.scale (-81149408928000) (sourceRows 1469)) merged1463 := by decide +kernel

theorem mergedZero1464 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1464 x = 0 := by
  rw [mergeCheck1464, Integer.Sparse.eval_merge]
  rw [mergedZero1463 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1465 : merged1465 = Integer.Sparse.merge merged1462 merged1464 := by decide +kernel

theorem mergedZero1465 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1465 x = 0 := by
  rw [mergeCheck1465, Integer.Sparse.eval_merge]
  rw [mergedZero1462 x h, mergedZero1464 x h]
  simp only [add_zero]

theorem mergeCheck1466 : merged1466 = Integer.Sparse.merge (Integer.Sparse.scale (22359741046636654080) (sourceRows 1472)) (Integer.Sparse.scale (15254492424608102400000) (sourceRows 1473)) := by decide +kernel

theorem mergedZero1466 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1466 x = 0 := by
  rw [mergeCheck1466, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1467 : merged1467 = Integer.Sparse.merge (Integer.Sparse.scale (64375906606381543219200) (sourceRows 1475)) (Integer.Sparse.scale (-46738605399165943603200) (sourceRows 1476)) := by decide +kernel

theorem mergedZero1467 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1467 x = 0 := by
  rw [mergeCheck1467, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1468 : merged1468 = Integer.Sparse.merge (Integer.Sparse.scale (7535140278757643059200) (sourceRows 1474)) merged1467 := by decide +kernel

theorem mergedZero1468 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1468 x = 0 := by
  rw [mergeCheck1468, Integer.Sparse.eval_merge]
  rw [mergedZero1467 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1469 : merged1469 = Integer.Sparse.merge merged1466 merged1468 := by decide +kernel

theorem mergedZero1469 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1469 x = 0 := by
  rw [mergeCheck1469, Integer.Sparse.eval_merge]
  rw [mergedZero1466 x h, mergedZero1468 x h]
  simp only [add_zero]

theorem mergeCheck1470 : merged1470 = Integer.Sparse.merge merged1465 merged1469 := by decide +kernel

theorem mergedZero1470 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1470 x = 0 := by
  rw [mergeCheck1470, Integer.Sparse.eval_merge]
  rw [mergedZero1465 x h, mergedZero1469 x h]
  simp only [add_zero]

theorem mergeCheck1471 : merged1471 = Integer.Sparse.merge merged1461 merged1470 := by decide +kernel

theorem mergedZero1471 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1471 x = 0 := by
  rw [mergeCheck1471, Integer.Sparse.eval_merge]
  rw [mergedZero1461 x h, mergedZero1470 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck1472 : merged1472 = Integer.Sparse.merge merged1453 merged1471 := by decide +kernel

theorem mergedZero1472 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1472 x = 0 := by
  rw [mergeCheck1472, Integer.Sparse.eval_merge]
  rw [mergedZero1453 x h, mergedZero1471 x h]
  simp only [add_zero]

theorem mergeCheck1473 : merged1473 = Integer.Sparse.merge (Integer.Sparse.scale (-81149408928000) (sourceRows 1477)) (Integer.Sparse.scale (173187470131200) (sourceRows 1478)) := by decide +kernel

theorem mergedZero1473 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1473 x = 0 := by
  rw [mergeCheck1473, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1474 : merged1474 = Integer.Sparse.merge (Integer.Sparse.scale (82845827582112000) (sourceRows 1479)) (Integer.Sparse.scale (32814812983848376320) (sourceRows 1480)) := by decide +kernel

theorem mergedZero1474 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1474 x = 0 := by
  rw [mergeCheck1474, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1475 : merged1475 = Integer.Sparse.merge merged1473 merged1474 := by decide +kernel

theorem mergedZero1475 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1475 x = 0 := by
  rw [mergeCheck1475, Integer.Sparse.eval_merge]
  rw [mergedZero1473 x h, mergedZero1474 x h]
  simp only [add_zero]

theorem mergeCheck1476 : merged1476 = Integer.Sparse.merge (Integer.Sparse.scale (-136081916191660574822400) (sourceRows 1481)) (Integer.Sparse.scale (-24408469453804240896000) (sourceRows 1482)) := by decide +kernel

theorem mergedZero1476 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1476 x = 0 := by
  rw [mergeCheck1476, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1477 : merged1477 = Integer.Sparse.merge (Integer.Sparse.scale (-314597437763253120) (sourceRows 1484)) (Integer.Sparse.scale (1326356724718061568000) (sourceRows 1485)) := by decide +kernel

theorem mergedZero1477 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1477 x = 0 := by
  rw [mergeCheck1477, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1478 : merged1478 = Integer.Sparse.merge (Integer.Sparse.scale (1326386975529369600000) (sourceRows 1483)) merged1477 := by decide +kernel

theorem mergedZero1478 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1478 x = 0 := by
  rw [mergeCheck1478, Integer.Sparse.eval_merge]
  rw [mergedZero1477 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1479 : merged1479 = Integer.Sparse.merge merged1476 merged1478 := by decide +kernel

theorem mergedZero1479 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1479 x = 0 := by
  rw [mergeCheck1479, Integer.Sparse.eval_merge]
  rw [mergedZero1476 x h, mergedZero1478 x h]
  simp only [add_zero]

theorem mergeCheck1480 : merged1480 = Integer.Sparse.merge merged1475 merged1479 := by decide +kernel

theorem mergedZero1480 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1480 x = 0 := by
  rw [mergeCheck1480, Integer.Sparse.eval_merge]
  rw [mergedZero1475 x h, mergedZero1479 x h]
  simp only [add_zero]

theorem mergeCheck1481 : merged1481 = Integer.Sparse.merge (Integer.Sparse.scale (1660758810383109427200) (sourceRows 1486)) (Integer.Sparse.scale (909044926782418944000) (sourceRows 1487)) := by decide +kernel

theorem mergedZero1481 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1481 x = 0 := by
  rw [mergeCheck1481, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1482 : merged1482 = Integer.Sparse.merge (Integer.Sparse.scale (-1723175787538959667200) (sourceRows 1489)) (Integer.Sparse.scale (811494089280000) (sourceRows 1490)) := by decide +kernel

theorem mergedZero1482 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1482 x = 0 := by
  rw [mergeCheck1482, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1483 : merged1483 = Integer.Sparse.merge (Integer.Sparse.scale (-3216811366993474252800) (sourceRows 1488)) merged1482 := by decide +kernel

theorem mergedZero1483 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1483 x = 0 := by
  rw [mergeCheck1483, Integer.Sparse.eval_merge]
  rw [mergedZero1482 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1484 : merged1484 = Integer.Sparse.merge merged1481 merged1483 := by decide +kernel

theorem mergedZero1484 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1484 x = 0 := by
  rw [mergeCheck1484, Integer.Sparse.eval_merge]
  rw [mergedZero1481 x h, mergedZero1483 x h]
  simp only [add_zero]

theorem mergeCheck1485 : merged1485 = Integer.Sparse.merge (Integer.Sparse.scale (78765351562541548800) (sourceRows 1491)) (Integer.Sparse.scale (288645783552000) (sourceRows 1492)) := by decide +kernel

theorem mergedZero1485 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1485 x = 0 := by
  rw [mergeCheck1485, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1486 : merged1486 = Integer.Sparse.merge (Integer.Sparse.scale (24545682691168585766400) (sourceRows 1494)) (Integer.Sparse.scale (-277418190741051782419200) (sourceRows 1495)) := by decide +kernel

theorem mergedZero1486 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1486 x = 0 := by
  rw [mergeCheck1486, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1487 : merged1487 = Integer.Sparse.merge (Integer.Sparse.scale (16407406491924188160) (sourceRows 1493)) merged1486 := by decide +kernel

theorem mergedZero1487 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1487 x = 0 := by
  rw [mergeCheck1487, Integer.Sparse.eval_merge]
  rw [mergedZero1486 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1488 : merged1488 = Integer.Sparse.merge merged1485 merged1487 := by decide +kernel

theorem mergedZero1488 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1488 x = 0 := by
  rw [mergeCheck1488, Integer.Sparse.eval_merge]
  rw [mergedZero1485 x h, mergedZero1487 x h]
  simp only [add_zero]

theorem mergeCheck1489 : merged1489 = Integer.Sparse.merge merged1484 merged1488 := by decide +kernel

theorem mergedZero1489 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1489 x = 0 := by
  rw [mergeCheck1489, Integer.Sparse.eval_merge]
  rw [mergedZero1484 x h, mergedZero1488 x h]
  simp only [add_zero]

theorem mergeCheck1490 : merged1490 = Integer.Sparse.merge merged1480 merged1489 := by decide +kernel

theorem mergedZero1490 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1490 x = 0 := by
  rw [mergeCheck1490, Integer.Sparse.eval_merge]
  rw [mergedZero1480 x h, mergedZero1489 x h]
  simp only [add_zero]

theorem mergeCheck1491 : merged1491 = Integer.Sparse.merge (Integer.Sparse.scale (-264740493945730521600) (sourceRows 1496)) (Integer.Sparse.scale (209349043152247238284800) (sourceRows 1497)) := by decide +kernel

theorem mergedZero1491 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1491 x = 0 := by
  rw [mergeCheck1491, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1492 : merged1492 = Integer.Sparse.merge (Integer.Sparse.scale (-9883620805888569600) (sourceRows 1498)) (Integer.Sparse.scale (-6672750076086796800) (sourceRows 1499)) := by decide +kernel

theorem mergedZero1492 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1492 x = 0 := by
  rw [mergeCheck1492, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1493 : merged1493 = Integer.Sparse.merge merged1491 merged1492 := by decide +kernel

theorem mergedZero1493 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1493 x = 0 := by
  rw [mergeCheck1493, Integer.Sparse.eval_merge]
  rw [mergedZero1491 x h, mergedZero1492 x h]
  simp only [add_zero]

theorem mergeCheck1494 : merged1494 = Integer.Sparse.merge (Integer.Sparse.scale (6659822516620492800) (sourceRows 1500)) (Integer.Sparse.scale (-68053263750035898163200) (sourceRows 1501)) := by decide +kernel

theorem mergedZero1494 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1494 x = 0 := by
  rw [mergeCheck1494, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1495 : merged1495 = Integer.Sparse.merge (Integer.Sparse.scale (12189939784131891801600) (sourceRows 1503)) (Integer.Sparse.scale (-19478899242369810331200) (sourceRows 1504)) := by decide +kernel

theorem mergedZero1495 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1495 x = 0 := by
  rw [mergeCheck1495, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1496 : merged1496 = Integer.Sparse.merge (Integer.Sparse.scale (68053263750035898163200) (sourceRows 1502)) merged1495 := by decide +kernel

theorem mergedZero1496 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1496 x = 0 := by
  rw [mergeCheck1496, Integer.Sparse.eval_merge]
  rw [mergedZero1495 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1497 : merged1497 = Integer.Sparse.merge merged1494 merged1496 := by decide +kernel

theorem mergedZero1497 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1497 x = 0 := by
  rw [mergeCheck1497, Integer.Sparse.eval_merge]
  rw [mergedZero1494 x h, mergedZero1496 x h]
  simp only [add_zero]

theorem mergeCheck1498 : merged1498 = Integer.Sparse.merge merged1493 merged1497 := by decide +kernel

theorem mergedZero1498 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1498 x = 0 := by
  rw [mergeCheck1498, Integer.Sparse.eval_merge]
  rw [mergedZero1493 x h, mergedZero1497 x h]
  simp only [add_zero]

theorem mergeCheck1499 : merged1499 = Integer.Sparse.merge (Integer.Sparse.scale (-1233183465238265856000) (sourceRows 1505)) (Integer.Sparse.scale (-1233236307865669632000) (sourceRows 1506)) := by decide +kernel

theorem mergedZero1499 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1499 x = 0 := by
  rw [mergeCheck1499, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1500 : merged1500 = Integer.Sparse.merge (Integer.Sparse.scale (1572675315738476544000) (sourceRows 1508)) (Integer.Sparse.scale (1572717164511015936000) (sourceRows 1509)) := by decide +kernel

theorem mergedZero1500 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1500 x = 0 := by
  rw [mergeCheck1500, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1501 : merged1501 = Integer.Sparse.merge (Integer.Sparse.scale (-144322891776000) (sourceRows 1507)) merged1500 := by decide +kernel

theorem mergedZero1501 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1501 x = 0 := by
  rw [mergeCheck1501, Integer.Sparse.eval_merge]
  rw [mergedZero1500 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1502 : merged1502 = Integer.Sparse.merge merged1499 merged1501 := by decide +kernel

theorem mergedZero1502 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1502 x = 0 := by
  rw [mergeCheck1502, Integer.Sparse.eval_merge]
  rw [mergedZero1499 x h, mergedZero1501 x h]
  simp only [add_zero]

theorem mergeCheck1503 : merged1503 = Integer.Sparse.merge (Integer.Sparse.scale (-81149408928000) (sourceRows 1510)) (Integer.Sparse.scale (-28864578355200) (sourceRows 1511)) := by decide +kernel

theorem mergedZero1503 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1503 x = 0 := by
  rw [mergeCheck1503, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

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

theorem mergeCheck1504 : merged1504 = Integer.Sparse.merge (Integer.Sparse.scale (-555246685776384000) (sourceRows 1513)) (Integer.Sparse.scale (-294730170448896000) (sourceRows 1514)) := by decide +kernel

theorem mergedZero1504 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1504 x = 0 := by
  rw [mergeCheck1504, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1505 : merged1505 = Integer.Sparse.merge (Integer.Sparse.scale (6147517599788745600) (sourceRows 1512)) merged1504 := by decide +kernel

theorem mergedZero1505 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1505 x = 0 := by
  rw [mergeCheck1505, Integer.Sparse.eval_merge]
  rw [mergedZero1504 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck1506 : merged1506 = Integer.Sparse.merge merged1503 merged1505 := by decide +kernel

theorem mergedZero1506 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1506 x = 0 := by
  rw [mergeCheck1506, Integer.Sparse.eval_merge]
  rw [mergedZero1503 x h, mergedZero1505 x h]
  simp only [add_zero]

theorem mergeCheck1507 : merged1507 = Integer.Sparse.merge merged1502 merged1506 := by decide +kernel

theorem mergedZero1507 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1507 x = 0 := by
  rw [mergeCheck1507, Integer.Sparse.eval_merge]
  rw [mergedZero1502 x h, mergedZero1506 x h]
  simp only [add_zero]

theorem mergeCheck1508 : merged1508 = Integer.Sparse.merge merged1498 merged1507 := by decide +kernel

theorem mergedZero1508 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1508 x = 0 := by
  rw [mergeCheck1508, Integer.Sparse.eval_merge]
  rw [mergedZero1498 x h, mergedZero1507 x h]
  simp only [add_zero]

theorem mergeCheck1509 : merged1509 = Integer.Sparse.merge merged1490 merged1508 := by decide +kernel

theorem mergedZero1509 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1509 x = 0 := by
  rw [mergeCheck1509, Integer.Sparse.eval_merge]
  rw [mergedZero1490 x h, mergedZero1508 x h]
  simp only [add_zero]

theorem mergeCheck1510 : merged1510 = Integer.Sparse.merge merged1472 merged1509 := by decide +kernel

theorem mergedZero1510 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1510 x = 0 := by
  rw [mergeCheck1510, Integer.Sparse.eval_merge]
  rw [mergedZero1472 x h, mergedZero1509 x h]
  simp only [add_zero]

theorem mergeCheck1511 : merged1511 = Integer.Sparse.merge merged1435 merged1510 := by decide +kernel

theorem mergedZero1511_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1511 x = 0 := by
  rw [mergeCheck1511, Integer.Sparse.eval_merge]
  rw [mergedZero1435 x h, mergedZero1510 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero1511_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero1511_e_oai
