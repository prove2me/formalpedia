-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero602_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:13:44.933238+00:00
-- url     : https://prove2.me/submissions/cf3750e8-c429-4e45-be9a-789425232573

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E067
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck452 : merged452 = Integer.Sparse.merge (Integer.Sparse.scale (23923884095553437940) (sourceRows 454)) (Integer.Sparse.scale (1102919437332769695811200) (sourceRows 455)) := by decide +kernel

theorem mergedZero452 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged452 x = 0 := by
  rw [mergeCheck452, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck453 : merged453 = Integer.Sparse.merge (Integer.Sparse.scale (2262194476458000) (sourceRows 456)) (Integer.Sparse.scale (35439998022556246425600) (sourceRows 457)) := by decide +kernel

theorem mergedZero453 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged453 x = 0 := by
  rw [mergeCheck453, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck454 : merged454 = Integer.Sparse.merge merged452 merged453 := by decide +kernel

theorem mergedZero454 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged454 x = 0 := by
  rw [mergeCheck454, Integer.Sparse.eval_merge]
  rw [mergedZero452 x h, mergedZero453 x h]
  simp only [add_zero]

theorem mergeCheck455 : merged455 = Integer.Sparse.merge (Integer.Sparse.scale (140127973067820305635200) (sourceRows 458)) (Integer.Sparse.scale (35439998022556246425600) (sourceRows 459)) := by decide +kernel

theorem mergedZero455 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged455 x = 0 := by
  rw [mergeCheck455, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck456 : merged456 = Integer.Sparse.merge (Integer.Sparse.scale (-12021372518400) (sourceRows 461)) (Integer.Sparse.scale (10701520573262882580) (sourceRows 462)) := by decide +kernel

theorem mergedZero456 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged456 x = 0 := by
  rw [mergeCheck456, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck457 : merged457 = Integer.Sparse.merge (Integer.Sparse.scale (761712267854734241875200) (sourceRows 460)) merged456 := by decide +kernel

theorem mergedZero457 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged457 x = 0 := by
  rw [mergeCheck457, Integer.Sparse.eval_merge]
  rw [mergedZero456 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck458 : merged458 = Integer.Sparse.merge merged455 merged457 := by decide +kernel

theorem mergedZero458 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged458 x = 0 := by
  rw [mergeCheck458, Integer.Sparse.eval_merge]
  rw [mergedZero455 x h, mergedZero457 x h]
  simp only [add_zero]

theorem mergeCheck459 : merged459 = Integer.Sparse.merge merged454 merged458 := by decide +kernel

theorem mergedZero459 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged459 x = 0 := by
  rw [mergeCheck459, Integer.Sparse.eval_merge]
  rw [mergedZero454 x h, mergedZero458 x h]
  simp only [add_zero]

theorem mergeCheck460 : merged460 = Integer.Sparse.merge (Integer.Sparse.scale (705912459146564880) (sourceRows 463)) (Integer.Sparse.scale (21589271685588217782578400) (sourceRows 464)) := by decide +kernel

theorem mergedZero460 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged460 x = 0 := by
  rw [mergeCheck460, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck461 : merged461 = Integer.Sparse.merge (Integer.Sparse.scale (2624621161814938490400000) (sourceRows 466)) (Integer.Sparse.scale (1643931283794440049309600) (sourceRows 467)) := by decide +kernel

theorem mergedZero461 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged461 x = 0 := by
  rw [mergeCheck461, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck462 : merged462 = Integer.Sparse.merge (Integer.Sparse.scale (-2624621161814938490400000) (sourceRows 465)) merged461 := by decide +kernel

theorem mergedZero462 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged462 x = 0 := by
  rw [mergeCheck462, Integer.Sparse.eval_merge]
  rw [mergedZero461 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck463 : merged463 = Integer.Sparse.merge merged460 merged462 := by decide +kernel

theorem mergedZero463 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged463 x = 0 := by
  rw [mergeCheck463, Integer.Sparse.eval_merge]
  rw [mergedZero460 x h, mergedZero462 x h]
  simp only [add_zero]

theorem mergeCheck464 : merged464 = Integer.Sparse.merge (Integer.Sparse.scale (-6398080732477321522790400) (sourceRows 468)) (Integer.Sparse.scale (2624621161814938490400000) (sourceRows 469)) := by decide +kernel

theorem mergedZero464 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged464 x = 0 := by
  rw [mergeCheck464, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck465 : merged465 = Integer.Sparse.merge (Integer.Sparse.scale (-640528149514643018899200) (sourceRows 471)) (Integer.Sparse.scale (380009274175336146364800) (sourceRows 472)) := by decide +kernel

theorem mergedZero465 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged465 x = 0 := by
  rw [mergeCheck465, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck466 : merged466 = Integer.Sparse.merge (Integer.Sparse.scale (5245019136000) (sourceRows 470)) merged465 := by decide +kernel

theorem mergedZero466 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged466 x = 0 := by
  rw [mergeCheck466, Integer.Sparse.eval_merge]
  rw [mergedZero465 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck467 : merged467 = Integer.Sparse.merge merged464 merged466 := by decide +kernel

theorem mergedZero467 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged467 x = 0 := by
  rw [mergeCheck467, Integer.Sparse.eval_merge]
  rw [mergedZero464 x h, mergedZero466 x h]
  simp only [add_zero]

theorem mergeCheck468 : merged468 = Integer.Sparse.merge merged463 merged467 := by decide +kernel

theorem mergedZero468 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged468 x = 0 := by
  rw [mergeCheck468, Integer.Sparse.eval_merge]
  rw [mergedZero463 x h, mergedZero467 x h]
  simp only [add_zero]

theorem mergeCheck469 : merged469 = Integer.Sparse.merge merged459 merged468 := by decide +kernel

theorem mergedZero469 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged469 x = 0 := by
  rw [mergeCheck469, Integer.Sparse.eval_merge]
  rw [mergedZero459 x h, mergedZero468 x h]
  simp only [add_zero]

theorem mergeCheck470 : merged470 = Integer.Sparse.merge (Integer.Sparse.scale (-12183903531299750460) (sourceRows 473)) (Integer.Sparse.scale (292204866708954988740) (sourceRows 474)) := by decide +kernel

theorem mergedZero470 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged470 x = 0 := by
  rw [mergeCheck470, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck471 : merged471 = Integer.Sparse.merge (Integer.Sparse.scale (3908670619180921440) (sourceRows 475)) (Integer.Sparse.scale (-11404185760705329398696400) (sourceRows 476)) := by decide +kernel

theorem mergedZero471 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged471 x = 0 := by
  rw [mergeCheck471, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck472 : merged472 = Integer.Sparse.merge merged470 merged471 := by decide +kernel

theorem mergedZero472 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged472 x = 0 := by
  rw [mergeCheck472, Integer.Sparse.eval_merge]
  rw [mergedZero470 x h, mergedZero471 x h]
  simp only [add_zero]

theorem mergeCheck473 : merged473 = Integer.Sparse.merge (Integer.Sparse.scale (360518840990154379814400) (sourceRows 477)) (Integer.Sparse.scale (-4874630580158394686400) (sourceRows 478)) := by decide +kernel

theorem mergedZero473 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged473 x = 0 := by
  rw [mergeCheck473, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck474 : merged474 = Integer.Sparse.merge (Integer.Sparse.scale (-246329175150239270745600) (sourceRows 480)) (Integer.Sparse.scale (-21404812553965441440) (sourceRows 481)) := by decide +kernel

theorem mergedZero474 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged474 x = 0 := by
  rw [mergeCheck474, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck475 : merged475 = Integer.Sparse.merge (Integer.Sparse.scale (513805639181441793580800) (sourceRows 479)) merged474 := by decide +kernel

theorem mergedZero475 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged475 x = 0 := by
  rw [mergeCheck475, Integer.Sparse.eval_merge]
  rw [mergedZero474 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck476 : merged476 = Integer.Sparse.merge merged473 merged475 := by decide +kernel

theorem mergedZero476 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged476 x = 0 := by
  rw [mergeCheck476, Integer.Sparse.eval_merge]
  rw [mergedZero473 x h, mergedZero475 x h]
  simp only [add_zero]

theorem mergeCheck477 : merged477 = Integer.Sparse.merge merged472 merged476 := by decide +kernel

theorem mergedZero477 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged477 x = 0 := by
  rw [mergeCheck477, Integer.Sparse.eval_merge]
  rw [mergedZero472 x h, mergedZero476 x h]
  simp only [add_zero]

theorem mergeCheck478 : merged478 = Integer.Sparse.merge (Integer.Sparse.scale (-28232174378819350800) (sourceRows 482)) (Integer.Sparse.scale (4711626408209817600) (sourceRows 483)) := by decide +kernel

theorem mergedZero478 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged478 x = 0 := by
  rw [mergeCheck478, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck479 : merged479 = Integer.Sparse.merge (Integer.Sparse.scale (1394695732754257920) (sourceRows 485)) (Integer.Sparse.scale (-1617503253761094853708800) (sourceRows 486)) := by decide +kernel

theorem mergedZero479 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged479 x = 0 := by
  rw [mergeCheck479, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck480 : merged480 = Integer.Sparse.merge (Integer.Sparse.scale (3148457604643804320) (sourceRows 484)) merged479 := by decide +kernel

theorem mergedZero480 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged480 x = 0 := by
  rw [mergeCheck480, Integer.Sparse.eval_merge]
  rw [mergedZero479 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck481 : merged481 = Integer.Sparse.merge merged478 merged480 := by decide +kernel

theorem mergedZero481 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged481 x = 0 := by
  rw [mergeCheck481, Integer.Sparse.eval_merge]
  rw [mergedZero478 x h, mergedZero480 x h]
  simp only [add_zero]

theorem mergeCheck482 : merged482 = Integer.Sparse.merge (Integer.Sparse.scale (3080326958701977600) (sourceRows 487)) (Integer.Sparse.scale (-20662332806699846735760) (sourceRows 488)) := by decide +kernel

theorem mergedZero482 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged482 x = 0 := by
  rw [mergeCheck482, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck483 : merged483 = Integer.Sparse.merge (Integer.Sparse.scale (-85262155012449282033936000) (sourceRows 490)) (Integer.Sparse.scale (41677998943626129304180800) (sourceRows 491)) := by decide +kernel

theorem mergedZero483 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged483 x = 0 := by
  rw [mergeCheck483, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck484 : merged484 = Integer.Sparse.merge (Integer.Sparse.scale (3080099083192296480) (sourceRows 489)) merged483 := by decide +kernel

theorem mergedZero484 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged484 x = 0 := by
  rw [mergeCheck484, Integer.Sparse.eval_merge]
  rw [mergedZero483 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck485 : merged485 = Integer.Sparse.merge merged482 merged484 := by decide +kernel

theorem mergedZero485 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged485 x = 0 := by
  rw [mergeCheck485, Integer.Sparse.eval_merge]
  rw [mergedZero482 x h, mergedZero484 x h]
  simp only [add_zero]

theorem mergeCheck486 : merged486 = Integer.Sparse.merge merged481 merged485 := by decide +kernel

theorem mergedZero486 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged486 x = 0 := by
  rw [mergeCheck486, Integer.Sparse.eval_merge]
  rw [mergedZero481 x h, mergedZero485 x h]
  simp only [add_zero]

theorem mergeCheck487 : merged487 = Integer.Sparse.merge merged477 merged486 := by decide +kernel

theorem mergedZero487 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged487 x = 0 := by
  rw [mergeCheck487, Integer.Sparse.eval_merge]
  rw [mergedZero477 x h, mergedZero486 x h]
  simp only [add_zero]

theorem mergeCheck488 : merged488 = Integer.Sparse.merge merged469 merged487 := by decide +kernel

theorem mergedZero488 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged488 x = 0 := by
  rw [mergeCheck488, Integer.Sparse.eval_merge]
  rw [mergedZero469 x h, mergedZero487 x h]
  simp only [add_zero]

theorem mergeCheck489 : merged489 = Integer.Sparse.merge (Integer.Sparse.scale (-20061551134686849404702400) (sourceRows 492)) (Integer.Sparse.scale (19166574991474048542264000) (sourceRows 493)) := by decide +kernel

theorem mergedZero489 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged489 x = 0 := by
  rw [mergeCheck489, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck490 : merged490 = Integer.Sparse.merge (Integer.Sparse.scale (20097712460788735896849600) (sourceRows 494)) (Integer.Sparse.scale (19472324730249546407044800) (sourceRows 495)) := by decide +kernel

theorem mergedZero490 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged490 x = 0 := by
  rw [mergeCheck490, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck491 : merged491 = Integer.Sparse.merge merged489 merged490 := by decide +kernel

theorem mergedZero491 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged491 x = 0 := by
  rw [mergeCheck491, Integer.Sparse.eval_merge]
  rw [mergedZero489 x h, mergedZero490 x h]
  simp only [add_zero]

theorem mergeCheck492 : merged492 = Integer.Sparse.merge (Integer.Sparse.scale (-19351203495382455550660800) (sourceRows 496)) (Integer.Sparse.scale (1424625121111920) (sourceRows 497)) := by decide +kernel

theorem mergedZero492 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged492 x = 0 := by
  rw [mergeCheck492, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck493 : merged493 = Integer.Sparse.merge (Integer.Sparse.scale (-23756897054207001720) (sourceRows 499)) (Integer.Sparse.scale (-2922391681854222480) (sourceRows 500)) := by decide +kernel

theorem mergedZero493 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged493 x = 0 := by
  rw [mergeCheck493, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck494 : merged494 = Integer.Sparse.merge (Integer.Sparse.scale (1992043152051120) (sourceRows 498)) merged493 := by decide +kernel

theorem mergedZero494 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged494 x = 0 := by
  rw [mergeCheck494, Integer.Sparse.eval_merge]
  rw [mergedZero493 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck495 : merged495 = Integer.Sparse.merge merged492 merged494 := by decide +kernel

theorem mergedZero495 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged495 x = 0 := by
  rw [mergeCheck495, Integer.Sparse.eval_merge]
  rw [mergedZero492 x h, mergedZero494 x h]
  simp only [add_zero]

theorem mergeCheck496 : merged496 = Integer.Sparse.merge merged491 merged495 := by decide +kernel

theorem mergedZero496 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged496 x = 0 := by
  rw [mergeCheck496, Integer.Sparse.eval_merge]
  rw [mergedZero491 x h, mergedZero495 x h]
  simp only [add_zero]

theorem mergeCheck497 : merged497 = Integer.Sparse.merge (Integer.Sparse.scale (-1482661021561433179200) (sourceRows 501)) (Integer.Sparse.scale (-1345713266301091564262400) (sourceRows 502)) := by decide +kernel

theorem mergedZero497 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged497 x = 0 := by
  rw [mergeCheck497, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck498 : merged498 = Integer.Sparse.merge (Integer.Sparse.scale (-112081589026853574240) (sourceRows 504)) (Integer.Sparse.scale (129548603291241960) (sourceRows 505)) := by decide +kernel

theorem mergedZero498 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged498 x = 0 := by
  rw [mergeCheck498, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck499 : merged499 = Integer.Sparse.merge (Integer.Sparse.scale (130537606955212800) (sourceRows 503)) merged498 := by decide +kernel

theorem mergedZero499 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged499 x = 0 := by
  rw [mergeCheck499, Integer.Sparse.eval_merge]
  rw [mergedZero498 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck500 : merged500 = Integer.Sparse.merge merged497 merged499 := by decide +kernel

theorem mergedZero500 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged500 x = 0 := by
  rw [mergeCheck500, Integer.Sparse.eval_merge]
  rw [mergedZero497 x h, mergedZero499 x h]
  simp only [add_zero]

theorem mergeCheck501 : merged501 = Integer.Sparse.merge (Integer.Sparse.scale (5377286064104618769352800) (sourceRows 506)) (Integer.Sparse.scale (-155620603721070437644800) (sourceRows 507)) := by decide +kernel

theorem mergedZero501 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged501 x = 0 := by
  rw [mergeCheck501, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck502 : merged502 = Integer.Sparse.merge (Integer.Sparse.scale (492792674493644526758400) (sourceRows 509)) (Integer.Sparse.scale (-72216055478098395360000) (sourceRows 510)) := by decide +kernel

theorem mergedZero502 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged502 x = 0 := by
  rw [mergeCheck502, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck503 : merged503 = Integer.Sparse.merge (Integer.Sparse.scale (382379314292936496144000) (sourceRows 508)) merged502 := by decide +kernel

theorem mergedZero503 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged503 x = 0 := by
  rw [mergeCheck503, Integer.Sparse.eval_merge]
  rw [mergedZero502 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck504 : merged504 = Integer.Sparse.merge merged501 merged503 := by decide +kernel

theorem mergedZero504 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged504 x = 0 := by
  rw [mergeCheck504, Integer.Sparse.eval_merge]
  rw [mergedZero501 x h, mergedZero503 x h]
  simp only [add_zero]

theorem mergeCheck505 : merged505 = Integer.Sparse.merge merged500 merged504 := by decide +kernel

theorem mergedZero505 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged505 x = 0 := by
  rw [mergeCheck505, Integer.Sparse.eval_merge]
  rw [mergedZero500 x h, mergedZero504 x h]
  simp only [add_zero]

theorem mergeCheck506 : merged506 = Integer.Sparse.merge merged496 merged505 := by decide +kernel

theorem mergedZero506 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged506 x = 0 := by
  rw [mergeCheck506, Integer.Sparse.eval_merge]
  rw [mergedZero496 x h, mergedZero505 x h]
  simp only [add_zero]

theorem mergeCheck507 : merged507 = Integer.Sparse.merge (Integer.Sparse.scale (-435746576531378272204800) (sourceRows 511)) (Integer.Sparse.scale (-552616995194880) (sourceRows 512)) := by decide +kernel

theorem mergedZero507 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged507 x = 0 := by
  rw [mergeCheck507, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck508 : merged508 = Integer.Sparse.merge (Integer.Sparse.scale (15165958124444400) (sourceRows 513)) (Integer.Sparse.scale (-19060807249848960120) (sourceRows 514)) := by decide +kernel

theorem mergedZero508 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged508 x = 0 := by
  rw [mergeCheck508, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck509 : merged509 = Integer.Sparse.merge merged507 merged508 := by decide +kernel

theorem mergedZero509 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged509 x = 0 := by
  rw [mergeCheck509, Integer.Sparse.eval_merge]
  rw [mergedZero507 x h, mergedZero508 x h]
  simp only [add_zero]

theorem mergeCheck510 : merged510 = Integer.Sparse.merge (Integer.Sparse.scale (89534136046864215000) (sourceRows 515)) (Integer.Sparse.scale (-117119959920204066000) (sourceRows 516)) := by decide +kernel

theorem mergedZero510 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged510 x = 0 := by
  rw [mergeCheck510, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck511 : merged511 = Integer.Sparse.merge (Integer.Sparse.scale (-258677993673590400) (sourceRows 518)) (Integer.Sparse.scale (-792414140206187772000) (sourceRows 519)) := by decide +kernel

theorem mergedZero511 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged511 x = 0 := by
  rw [mergeCheck511, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck512 : merged512 = Integer.Sparse.merge (Integer.Sparse.scale (415437001054366373913600) (sourceRows 517)) merged511 := by decide +kernel

theorem mergedZero512 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged512 x = 0 := by
  rw [mergeCheck512, Integer.Sparse.eval_merge]
  rw [mergedZero511 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck513 : merged513 = Integer.Sparse.merge merged510 merged512 := by decide +kernel

theorem mergedZero513 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged513 x = 0 := by
  rw [mergeCheck513, Integer.Sparse.eval_merge]
  rw [mergedZero510 x h, mergedZero512 x h]
  simp only [add_zero]

theorem mergeCheck514 : merged514 = Integer.Sparse.merge merged509 merged513 := by decide +kernel

theorem mergedZero514 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged514 x = 0 := by
  rw [mergeCheck514, Integer.Sparse.eval_merge]
  rw [mergedZero509 x h, mergedZero513 x h]
  simp only [add_zero]

theorem mergeCheck515 : merged515 = Integer.Sparse.merge (Integer.Sparse.scale (-230601606939648000) (sourceRows 520)) (Integer.Sparse.scale (-109595641666916413260) (sourceRows 521)) := by decide +kernel

theorem mergedZero515 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged515 x = 0 := by
  rw [mergeCheck515, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck516 : merged516 = Integer.Sparse.merge (Integer.Sparse.scale (-36896508839357173440) (sourceRows 523)) (Integer.Sparse.scale (8990789599077696060) (sourceRows 524)) := by decide +kernel

theorem mergedZero516 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged516 x = 0 := by
  rw [mergeCheck516, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck517 : merged517 = Integer.Sparse.merge (Integer.Sparse.scale (-225320065717220901000) (sourceRows 522)) merged516 := by decide +kernel

theorem mergedZero517 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged517 x = 0 := by
  rw [mergeCheck517, Integer.Sparse.eval_merge]
  rw [mergedZero516 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck518 : merged518 = Integer.Sparse.merge merged515 merged517 := by decide +kernel

theorem mergedZero518 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged518 x = 0 := by
  rw [mergeCheck518, Integer.Sparse.eval_merge]
  rw [mergedZero515 x h, mergedZero517 x h]
  simp only [add_zero]

theorem mergeCheck519 : merged519 = Integer.Sparse.merge (Integer.Sparse.scale (-20022831281589644486160) (sourceRows 525)) (Integer.Sparse.scale (14274028859637513540) (sourceRows 526)) := by decide +kernel

theorem mergedZero519 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged519 x = 0 := by
  rw [mergeCheck519, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck520 : merged520 = Integer.Sparse.merge (Integer.Sparse.scale (-21233051037524244580502400) (sourceRows 528)) (Integer.Sparse.scale (-10624304107133500792478400) (sourceRows 529)) := by decide +kernel

theorem mergedZero520 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged520 x = 0 := by
  rw [mergeCheck520, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck521 : merged521 = Integer.Sparse.merge (Integer.Sparse.scale (3439648078803222540685200) (sourceRows 527)) merged520 := by decide +kernel

theorem mergedZero521 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged521 x = 0 := by
  rw [mergeCheck521, Integer.Sparse.eval_merge]
  rw [mergedZero520 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck522 : merged522 = Integer.Sparse.merge merged519 merged521 := by decide +kernel

theorem mergedZero522 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged522 x = 0 := by
  rw [mergeCheck522, Integer.Sparse.eval_merge]
  rw [mergedZero519 x h, mergedZero521 x h]
  simp only [add_zero]

theorem mergeCheck523 : merged523 = Integer.Sparse.merge merged518 merged522 := by decide +kernel

theorem mergedZero523 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged523 x = 0 := by
  rw [mergeCheck523, Integer.Sparse.eval_merge]
  rw [mergedZero518 x h, mergedZero522 x h]
  simp only [add_zero]

theorem mergeCheck524 : merged524 = Integer.Sparse.merge merged514 merged523 := by decide +kernel

theorem mergedZero524 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged524 x = 0 := by
  rw [mergeCheck524, Integer.Sparse.eval_merge]
  rw [mergedZero514 x h, mergedZero523 x h]
  simp only [add_zero]

theorem mergeCheck525 : merged525 = Integer.Sparse.merge merged506 merged524 := by decide +kernel

theorem mergedZero525 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged525 x = 0 := by
  rw [mergeCheck525, Integer.Sparse.eval_merge]
  rw [mergedZero506 x h, mergedZero524 x h]
  simp only [add_zero]

theorem mergeCheck526 : merged526 = Integer.Sparse.merge merged488 merged525 := by decide +kernel

theorem mergedZero526 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged526 x = 0 := by
  rw [mergeCheck526, Integer.Sparse.eval_merge]
  rw [mergedZero488 x h, mergedZero525 x h]
  simp only [add_zero]

theorem mergeCheck527 : merged527 = Integer.Sparse.merge (Integer.Sparse.scale (10399400319629478341318400) (sourceRows 530)) (Integer.Sparse.scale (-3268566477850800) (sourceRows 531)) := by decide +kernel

theorem mergedZero527 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged527 x = 0 := by
  rw [mergeCheck527, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck528 : merged528 = Integer.Sparse.merge (Integer.Sparse.scale (-30452144097085200) (sourceRows 532)) (Integer.Sparse.scale (29554338796537996980) (sourceRows 533)) := by decide +kernel

theorem mergedZero528 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged528 x = 0 := by
  rw [mergeCheck528, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck529 : merged529 = Integer.Sparse.merge merged527 merged528 := by decide +kernel

theorem mergedZero529 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged529 x = 0 := by
  rw [mergeCheck529, Integer.Sparse.eval_merge]
  rw [mergedZero527 x h, mergedZero528 x h]
  simp only [add_zero]

theorem mergeCheck530 : merged530 = Integer.Sparse.merge (Integer.Sparse.scale (7566756336882783600) (sourceRows 534)) (Integer.Sparse.scale (-426378585003274272902400) (sourceRows 535)) := by decide +kernel

theorem mergedZero530 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged530 x = 0 := by
  rw [mergeCheck530, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck531 : merged531 = Integer.Sparse.merge (Integer.Sparse.scale (89749670225436024300) (sourceRows 537)) (Integer.Sparse.scale (7328778819040166460) (sourceRows 538)) := by decide +kernel

theorem mergedZero531 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged531 x = 0 := by
  rw [mergeCheck531, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck532 : merged532 = Integer.Sparse.merge (Integer.Sparse.scale (-116809044584715483840000) (sourceRows 536)) merged531 := by decide +kernel

theorem mergedZero532 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged532 x = 0 := by
  rw [mergeCheck532, Integer.Sparse.eval_merge]
  rw [mergedZero531 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck533 : merged533 = Integer.Sparse.merge merged530 merged532 := by decide +kernel

theorem mergedZero533 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged533 x = 0 := by
  rw [mergeCheck533, Integer.Sparse.eval_merge]
  rw [mergedZero530 x h, mergedZero532 x h]
  simp only [add_zero]

theorem mergeCheck534 : merged534 = Integer.Sparse.merge merged529 merged533 := by decide +kernel

theorem mergedZero534 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged534 x = 0 := by
  rw [mergeCheck534, Integer.Sparse.eval_merge]
  rw [mergedZero529 x h, mergedZero533 x h]
  simp only [add_zero]

theorem mergeCheck535 : merged535 = Integer.Sparse.merge (Integer.Sparse.scale (165212800847596661040) (sourceRows 539)) (Integer.Sparse.scale (-53843262318688557120) (sourceRows 540)) := by decide +kernel

theorem mergedZero535 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged535 x = 0 := by
  rw [mergeCheck535, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck536 : merged536 = Integer.Sparse.merge (Integer.Sparse.scale (-2775535815654604800) (sourceRows 542)) (Integer.Sparse.scale (-2032636057914996240) (sourceRows 543)) := by decide +kernel

theorem mergedZero536 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged536 x = 0 := by
  rw [mergeCheck536, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck537 : merged537 = Integer.Sparse.merge (Integer.Sparse.scale (1642407838710240) (sourceRows 541)) merged536 := by decide +kernel

theorem mergedZero537 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged537 x = 0 := by
  rw [mergeCheck537, Integer.Sparse.eval_merge]
  rw [mergedZero536 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck538 : merged538 = Integer.Sparse.merge merged535 merged537 := by decide +kernel

theorem mergedZero538 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged538 x = 0 := by
  rw [mergeCheck538, Integer.Sparse.eval_merge]
  rw [mergedZero535 x h, mergedZero537 x h]
  simp only [add_zero]

theorem mergeCheck539 : merged539 = Integer.Sparse.merge (Integer.Sparse.scale (-329906916266882364446400) (sourceRows 544)) (Integer.Sparse.scale (7876942806040061040) (sourceRows 545)) := by decide +kernel

theorem mergedZero539 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged539 x = 0 := by
  rw [mergeCheck539, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck540 : merged540 = Integer.Sparse.merge (Integer.Sparse.scale (953762688732540511440) (sourceRows 547)) (Integer.Sparse.scale (98572576517806161120) (sourceRows 548)) := by decide +kernel

theorem mergedZero540 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged540 x = 0 := by
  rw [mergeCheck540, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck541 : merged541 = Integer.Sparse.merge (Integer.Sparse.scale (-84694375987956040320) (sourceRows 546)) merged540 := by decide +kernel

theorem mergedZero541 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged541 x = 0 := by
  rw [mergeCheck541, Integer.Sparse.eval_merge]
  rw [mergedZero540 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck542 : merged542 = Integer.Sparse.merge merged539 merged541 := by decide +kernel

theorem mergedZero542 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged542 x = 0 := by
  rw [mergeCheck542, Integer.Sparse.eval_merge]
  rw [mergedZero539 x h, mergedZero541 x h]
  simp only [add_zero]

theorem mergeCheck543 : merged543 = Integer.Sparse.merge merged538 merged542 := by decide +kernel

theorem mergedZero543 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged543 x = 0 := by
  rw [mergeCheck543, Integer.Sparse.eval_merge]
  rw [mergedZero538 x h, mergedZero542 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck544 : merged544 = Integer.Sparse.merge merged534 merged543 := by decide +kernel

theorem mergedZero544 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged544 x = 0 := by
  rw [mergeCheck544, Integer.Sparse.eval_merge]
  rw [mergedZero534 x h, mergedZero543 x h]
  simp only [add_zero]

theorem mergeCheck545 : merged545 = Integer.Sparse.merge (Integer.Sparse.scale (-272283492383569061035200) (sourceRows 549)) (Integer.Sparse.scale (764909131377984744816000) (sourceRows 550)) := by decide +kernel

theorem mergedZero545 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged545 x = 0 := by
  rw [mergeCheck545, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck546 : merged546 = Integer.Sparse.merge (Integer.Sparse.scale (-513761491691280) (sourceRows 551)) (Integer.Sparse.scale (-6740253119331828180) (sourceRows 552)) := by decide +kernel

theorem mergedZero546 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged546 x = 0 := by
  rw [mergeCheck546, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck547 : merged547 = Integer.Sparse.merge merged545 merged546 := by decide +kernel

theorem mergedZero547 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged547 x = 0 := by
  rw [mergeCheck547, Integer.Sparse.eval_merge]
  rw [mergedZero545 x h, mergedZero546 x h]
  simp only [add_zero]

theorem mergeCheck548 : merged548 = Integer.Sparse.merge (Integer.Sparse.scale (11512184187403468800) (sourceRows 553)) (Integer.Sparse.scale (-18007345267944655980) (sourceRows 554)) := by decide +kernel

theorem mergedZero548 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged548 x = 0 := by
  rw [mergeCheck548, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck549 : merged549 = Integer.Sparse.merge (Integer.Sparse.scale (10729008686954007726444000) (sourceRows 556)) (Integer.Sparse.scale (177088405745664000) (sourceRows 557)) := by decide +kernel

theorem mergedZero549 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged549 x = 0 := by
  rw [mergeCheck549, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck550 : merged550 = Integer.Sparse.merge (Integer.Sparse.scale (457289999128936180620) (sourceRows 555)) merged549 := by decide +kernel

theorem mergedZero550 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged550 x = 0 := by
  rw [mergeCheck550, Integer.Sparse.eval_merge]
  rw [mergedZero549 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck551 : merged551 = Integer.Sparse.merge merged548 merged550 := by decide +kernel

theorem mergedZero551 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged551 x = 0 := by
  rw [mergeCheck551, Integer.Sparse.eval_merge]
  rw [mergedZero548 x h, mergedZero550 x h]
  simp only [add_zero]

theorem mergeCheck552 : merged552 = Integer.Sparse.merge merged547 merged551 := by decide +kernel

theorem mergedZero552 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged552 x = 0 := by
  rw [mergeCheck552, Integer.Sparse.eval_merge]
  rw [mergedZero547 x h, mergedZero551 x h]
  simp only [add_zero]

theorem mergeCheck553 : merged553 = Integer.Sparse.merge (Integer.Sparse.scale (1905127117266723840) (sourceRows 558)) (Integer.Sparse.scale (6199059406455322260739200) (sourceRows 559)) := by decide +kernel

theorem mergedZero553 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged553 x = 0 := by
  rw [mergeCheck553, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck554 : merged554 = Integer.Sparse.merge (Integer.Sparse.scale (-21226269774614135459860800) (sourceRows 561)) (Integer.Sparse.scale (-10503879729421363543591200) (sourceRows 562)) := by decide +kernel

theorem mergedZero554 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged554 x = 0 := by
  rw [mergeCheck554, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck555 : merged555 = Integer.Sparse.merge (Integer.Sparse.scale (21554797093663140081432000) (sourceRows 560)) merged554 := by decide +kernel

theorem mergedZero555 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged555 x = 0 := by
  rw [mergeCheck555, Integer.Sparse.eval_merge]
  rw [mergedZero554 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck556 : merged556 = Integer.Sparse.merge merged553 merged555 := by decide +kernel

theorem mergedZero556 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged556 x = 0 := by
  rw [mergeCheck556, Integer.Sparse.eval_merge]
  rw [mergedZero553 x h, mergedZero555 x h]
  simp only [add_zero]

theorem mergeCheck557 : merged557 = Integer.Sparse.merge (Integer.Sparse.scale (4570280431459497614865600) (sourceRows 563)) (Integer.Sparse.scale (14274542897608838880) (sourceRows 564)) := by decide +kernel

theorem mergedZero557 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged557 x = 0 := by
  rw [mergeCheck557, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck558 : merged558 = Integer.Sparse.merge (Integer.Sparse.scale (-85215781943942267520) (sourceRows 566)) (Integer.Sparse.scale (24513519095646875700) (sourceRows 567)) := by decide +kernel

theorem mergedZero558 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged558 x = 0 := by
  rw [mergeCheck558, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck559 : merged559 = Integer.Sparse.merge (Integer.Sparse.scale (156982192892731222800) (sourceRows 565)) merged558 := by decide +kernel

theorem mergedZero559 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged559 x = 0 := by
  rw [mergeCheck559, Integer.Sparse.eval_merge]
  rw [mergedZero558 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck560 : merged560 = Integer.Sparse.merge merged557 merged559 := by decide +kernel

theorem mergedZero560 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged560 x = 0 := by
  rw [mergeCheck560, Integer.Sparse.eval_merge]
  rw [mergedZero557 x h, mergedZero559 x h]
  simp only [add_zero]

theorem mergeCheck561 : merged561 = Integer.Sparse.merge merged556 merged560 := by decide +kernel

theorem mergedZero561 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged561 x = 0 := by
  rw [mergeCheck561, Integer.Sparse.eval_merge]
  rw [mergedZero556 x h, mergedZero560 x h]
  simp only [add_zero]

theorem mergeCheck562 : merged562 = Integer.Sparse.merge merged552 merged561 := by decide +kernel

theorem mergedZero562 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged562 x = 0 := by
  rw [mergeCheck562, Integer.Sparse.eval_merge]
  rw [mergedZero552 x h, mergedZero561 x h]
  simp only [add_zero]

theorem mergeCheck563 : merged563 = Integer.Sparse.merge merged544 merged562 := by decide +kernel

theorem mergedZero563 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged563 x = 0 := by
  rw [mergeCheck563, Integer.Sparse.eval_merge]
  rw [mergedZero544 x h, mergedZero562 x h]
  simp only [add_zero]

theorem mergeCheck564 : merged564 = Integer.Sparse.merge (Integer.Sparse.scale (470035070522106522300) (sourceRows 568)) (Integer.Sparse.scale (313625158664739989961600) (sourceRows 569)) := by decide +kernel

theorem mergedZero564 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged564 x = 0 := by
  rw [mergeCheck564, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck565 : merged565 = Integer.Sparse.merge (Integer.Sparse.scale (-68005604994850368300) (sourceRows 570)) (Integer.Sparse.scale (1980085524341916811680) (sourceRows 571)) := by decide +kernel

theorem mergedZero565 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged565 x = 0 := by
  rw [mergeCheck565, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck566 : merged566 = Integer.Sparse.merge merged564 merged565 := by decide +kernel

theorem mergedZero566 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged566 x = 0 := by
  rw [mergeCheck566, Integer.Sparse.eval_merge]
  rw [mergedZero564 x h, mergedZero565 x h]
  simp only [add_zero]

theorem mergeCheck567 : merged567 = Integer.Sparse.merge (Integer.Sparse.scale (-142141310975266417500) (sourceRows 572)) (Integer.Sparse.scale (-18152723479978807562152800) (sourceRows 573)) := by decide +kernel

theorem mergedZero567 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged567 x = 0 := by
  rw [mergeCheck567, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck568 : merged568 = Integer.Sparse.merge (Integer.Sparse.scale (-7939348388633481807355200) (sourceRows 575)) (Integer.Sparse.scale (-4235254775699711849668800) (sourceRows 576)) := by decide +kernel

theorem mergedZero568 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged568 x = 0 := by
  rw [mergeCheck568, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck569 : merged569 = Integer.Sparse.merge (Integer.Sparse.scale (4152448497164735064074400) (sourceRows 574)) merged568 := by decide +kernel

theorem mergedZero569 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged569 x = 0 := by
  rw [mergeCheck569, Integer.Sparse.eval_merge]
  rw [mergedZero568 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck570 : merged570 = Integer.Sparse.merge merged567 merged569 := by decide +kernel

theorem mergedZero570 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged570 x = 0 := by
  rw [mergeCheck570, Integer.Sparse.eval_merge]
  rw [mergedZero567 x h, mergedZero569 x h]
  simp only [add_zero]

theorem mergeCheck571 : merged571 = Integer.Sparse.merge merged566 merged570 := by decide +kernel

theorem mergedZero571 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged571 x = 0 := by
  rw [mergeCheck571, Integer.Sparse.eval_merge]
  rw [mergedZero566 x h, mergedZero570 x h]
  simp only [add_zero]

theorem mergeCheck572 : merged572 = Integer.Sparse.merge (Integer.Sparse.scale (-7888261067200177183447200) (sourceRows 577)) (Integer.Sparse.scale (2825813859845054400) (sourceRows 578)) := by decide +kernel

theorem mergedZero572 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged572 x = 0 := by
  rw [mergeCheck572, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck573 : merged573 = Integer.Sparse.merge (Integer.Sparse.scale (-307986194130004686240) (sourceRows 580)) (Integer.Sparse.scale (-27655801564873539120) (sourceRows 581)) := by decide +kernel

theorem mergedZero573 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged573 x = 0 := by
  rw [mergeCheck573, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck574 : merged574 = Integer.Sparse.merge (Integer.Sparse.scale (-37157380355554860240) (sourceRows 579)) merged573 := by decide +kernel

theorem mergedZero574 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged574 x = 0 := by
  rw [mergeCheck574, Integer.Sparse.eval_merge]
  rw [mergedZero573 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck575 : merged575 = Integer.Sparse.merge merged572 merged574 := by decide +kernel

theorem mergedZero575 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged575 x = 0 := by
  rw [mergeCheck575, Integer.Sparse.eval_merge]
  rw [mergedZero572 x h, mergedZero574 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck576 : merged576 = Integer.Sparse.merge (Integer.Sparse.scale (1104992945339945215680) (sourceRows 582)) (Integer.Sparse.scale (103205894892569411846400) (sourceRows 583)) := by decide +kernel

theorem mergedZero576 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged576 x = 0 := by
  rw [mergeCheck576, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck577 : merged577 = Integer.Sparse.merge (Integer.Sparse.scale (-118398007092760615080) (sourceRows 585)) (Integer.Sparse.scale (-175167702521815333780800) (sourceRows 586)) := by decide +kernel

theorem mergedZero577 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged577 x = 0 := by
  rw [mergeCheck577, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck578 : merged578 = Integer.Sparse.merge (Integer.Sparse.scale (-149330530640018515200) (sourceRows 584)) merged577 := by decide +kernel

theorem mergedZero578 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged578 x = 0 := by
  rw [mergeCheck578, Integer.Sparse.eval_merge]
  rw [mergedZero577 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck579 : merged579 = Integer.Sparse.merge merged576 merged578 := by decide +kernel

theorem mergedZero579 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged579 x = 0 := by
  rw [mergeCheck579, Integer.Sparse.eval_merge]
  rw [mergedZero576 x h, mergedZero578 x h]
  simp only [add_zero]

theorem mergeCheck580 : merged580 = Integer.Sparse.merge merged575 merged579 := by decide +kernel

theorem mergedZero580 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged580 x = 0 := by
  rw [mergeCheck580, Integer.Sparse.eval_merge]
  rw [mergedZero575 x h, mergedZero579 x h]
  simp only [add_zero]

theorem mergeCheck581 : merged581 = Integer.Sparse.merge merged571 merged580 := by decide +kernel

theorem mergedZero581 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged581 x = 0 := by
  rw [mergeCheck581, Integer.Sparse.eval_merge]
  rw [mergedZero571 x h, mergedZero580 x h]
  simp only [add_zero]

theorem mergeCheck582 : merged582 = Integer.Sparse.merge (Integer.Sparse.scale (76421540574112195980) (sourceRows 587)) (Integer.Sparse.scale (-214605441560565422640) (sourceRows 588)) := by decide +kernel

theorem mergedZero582 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged582 x = 0 := by
  rw [mergeCheck582, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck583 : merged583 = Integer.Sparse.merge (Integer.Sparse.scale (242323613839699698600) (sourceRows 589)) (Integer.Sparse.scale (-944636674949188667208) (sourceRows 590)) := by decide +kernel

theorem mergedZero583 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged583 x = 0 := by
  rw [mergeCheck583, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck584 : merged584 = Integer.Sparse.merge merged582 merged583 := by decide +kernel

theorem mergedZero584 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged584 x = 0 := by
  rw [mergeCheck584, Integer.Sparse.eval_merge]
  rw [mergedZero582 x h, mergedZero583 x h]
  simp only [add_zero]

theorem mergeCheck585 : merged585 = Integer.Sparse.merge (Integer.Sparse.scale (146753235014400) (sourceRows 591)) (Integer.Sparse.scale (1155245683304160) (sourceRows 592)) := by decide +kernel

theorem mergedZero585 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged585 x = 0 := by
  rw [mergeCheck585, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck586 : merged586 = Integer.Sparse.merge (Integer.Sparse.scale (924560924067171910310400) (sourceRows 594)) (Integer.Sparse.scale (-743754763432085156236800) (sourceRows 595)) := by decide +kernel

theorem mergedZero586 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged586 x = 0 := by
  rw [mergeCheck586, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck587 : merged587 = Integer.Sparse.merge (Integer.Sparse.scale (891936739272683821248000) (sourceRows 593)) merged586 := by decide +kernel

theorem mergedZero587 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged587 x = 0 := by
  rw [mergeCheck587, Integer.Sparse.eval_merge]
  rw [mergedZero586 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck588 : merged588 = Integer.Sparse.merge merged585 merged587 := by decide +kernel

theorem mergedZero588 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged588 x = 0 := by
  rw [mergeCheck588, Integer.Sparse.eval_merge]
  rw [mergedZero585 x h, mergedZero587 x h]
  simp only [add_zero]

theorem mergeCheck589 : merged589 = Integer.Sparse.merge merged584 merged588 := by decide +kernel

theorem mergedZero589 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged589 x = 0 := by
  rw [mergeCheck589, Integer.Sparse.eval_merge]
  rw [mergedZero584 x h, mergedZero588 x h]
  simp only [add_zero]

theorem mergeCheck590 : merged590 = Integer.Sparse.merge (Integer.Sparse.scale (512809162802333248924800) (sourceRows 596)) (Integer.Sparse.scale (-841128018421712128128000) (sourceRows 597)) := by decide +kernel

theorem mergedZero590 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged590 x = 0 := by
  rw [mergeCheck590, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck591 : merged591 = Integer.Sparse.merge (Integer.Sparse.scale (30053431296000) (sourceRows 599)) (Integer.Sparse.scale (-2117737377439694640) (sourceRows 600)) := by decide +kernel

theorem mergedZero591 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged591 x = 0 := by
  rw [mergeCheck591, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck592 : merged592 = Integer.Sparse.merge (Integer.Sparse.scale (1845697176675359943667200) (sourceRows 598)) merged591 := by decide +kernel

theorem mergedZero592 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged592 x = 0 := by
  rw [mergeCheck592, Integer.Sparse.eval_merge]
  rw [mergedZero591 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck593 : merged593 = Integer.Sparse.merge merged590 merged592 := by decide +kernel

theorem mergedZero593 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged593 x = 0 := by
  rw [mergeCheck593, Integer.Sparse.eval_merge]
  rw [mergedZero590 x h, mergedZero592 x h]
  simp only [add_zero]

theorem mergeCheck594 : merged594 = Integer.Sparse.merge (Integer.Sparse.scale (-10701520573262882580) (sourceRows 601)) (Integer.Sparse.scale (7275467127138393076336800) (sourceRows 602)) := by decide +kernel

theorem mergedZero594 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged594 x = 0 := by
  rw [mergeCheck594, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck595 : merged595 = Integer.Sparse.merge (Integer.Sparse.scale (3937230368372012180263200) (sourceRows 604)) (Integer.Sparse.scale (7706092869166725439560000) (sourceRows 605)) := by decide +kernel

theorem mergedZero595 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged595 x = 0 := by
  rw [mergeCheck595, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck596 : merged596 = Integer.Sparse.merge (Integer.Sparse.scale (-4268552445609378539709600) (sourceRows 603)) merged595 := by decide +kernel

theorem mergedZero596 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged596 x = 0 := by
  rw [mergeCheck596, Integer.Sparse.eval_merge]
  rw [mergedZero595 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck597 : merged597 = Integer.Sparse.merge merged594 merged596 := by decide +kernel

theorem mergedZero597 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged597 x = 0 := by
  rw [mergeCheck597, Integer.Sparse.eval_merge]
  rw [mergedZero594 x h, mergedZero596 x h]
  simp only [add_zero]

theorem mergeCheck598 : merged598 = Integer.Sparse.merge merged593 merged597 := by decide +kernel

theorem mergedZero598 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged598 x = 0 := by
  rw [mergeCheck598, Integer.Sparse.eval_merge]
  rw [mergedZero593 x h, mergedZero597 x h]
  simp only [add_zero]

theorem mergeCheck599 : merged599 = Integer.Sparse.merge merged589 merged598 := by decide +kernel

theorem mergedZero599 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged599 x = 0 := by
  rw [mergeCheck599, Integer.Sparse.eval_merge]
  rw [mergedZero589 x h, mergedZero598 x h]
  simp only [add_zero]

theorem mergeCheck600 : merged600 = Integer.Sparse.merge merged581 merged599 := by decide +kernel

theorem mergedZero600 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged600 x = 0 := by
  rw [mergeCheck600, Integer.Sparse.eval_merge]
  rw [mergedZero581 x h, mergedZero599 x h]
  simp only [add_zero]

theorem mergeCheck601 : merged601 = Integer.Sparse.merge merged563 merged600 := by decide +kernel

theorem mergedZero601 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged601 x = 0 := by
  rw [mergeCheck601, Integer.Sparse.eval_merge]
  rw [mergedZero563 x h, mergedZero600 x h]
  simp only [add_zero]

theorem mergeCheck602 : merged602 = Integer.Sparse.merge merged526 merged601 := by decide +kernel

theorem mergedZero602_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged602 x = 0 := by
  rw [mergeCheck602, Integer.Sparse.eval_merge]
  rw [mergedZero526 x h, mergedZero601 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero602_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero602_e_oai
