-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero754_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:46:27.71367+00:00
-- url     : https://prove2.me/submissions/54d9add4-67b9-4837-9704-5ffca71e0a30

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E185
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck605 : merged605 = Integer.Sparse.merge (Integer.Sparse.scale (-26162538932865892036334400) (sourceRows 606)) (Integer.Sparse.scale (-1245475820332800) (sourceRows 607)) := by decide +kernel

theorem mergedZero605 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged605 x = 0 := by
  rw [mergeCheck605, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck606 : merged606 = Integer.Sparse.merge (Integer.Sparse.scale (6227379101664000) (sourceRows 608)) (Integer.Sparse.scale (2056294943938576956182400) (sourceRows 609)) := by decide +kernel

theorem mergedZero606 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged606 x = 0 := by
  rw [mergeCheck606, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck607 : merged607 = Integer.Sparse.merge merged605 merged606 := by decide +kernel

theorem mergedZero607 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged607 x = 0 := by
  rw [mergeCheck607, Integer.Sparse.eval_merge]
  rw [mergedZero605 x h, mergedZero606 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck608 : merged608 = Integer.Sparse.merge (Integer.Sparse.scale (743754796142823986572800) (sourceRows 610)) (Integer.Sparse.scale (-921382496851495909708800) (sourceRows 611)) := by decide +kernel

theorem mergedZero608 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged608 x = 0 := by
  rw [mergeCheck608, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck609 : merged609 = Integer.Sparse.merge (Integer.Sparse.scale (738295979548824480) (sourceRows 613)) (Integer.Sparse.scale (64212136134583653720) (sourceRows 614)) := by decide +kernel

theorem mergedZero609 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged609 x = 0 := by
  rw [mergeCheck609, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck610 : merged610 = Integer.Sparse.merge (Integer.Sparse.scale (-57729156710400) (sourceRows 612)) merged609 := by decide +kernel

theorem mergedZero610 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged610 x = 0 := by
  rw [mergeCheck610, Integer.Sparse.eval_merge]
  rw [mergedZero609 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck611 : merged611 = Integer.Sparse.merge merged608 merged610 := by decide +kernel

theorem mergedZero611 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged611 x = 0 := by
  rw [mergeCheck611, Integer.Sparse.eval_merge]
  rw [mergedZero608 x h, mergedZero610 x h]
  simp only [add_zero]

theorem mergeCheck612 : merged612 = Integer.Sparse.merge merged607 merged611 := by decide +kernel

theorem mergedZero612 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged612 x = 0 := by
  rw [mergeCheck612, Integer.Sparse.eval_merge]
  rw [mergedZero607 x h, mergedZero611 x h]
  simp only [add_zero]

theorem mergeCheck613 : merged613 = Integer.Sparse.merge (Integer.Sparse.scale (-14090131729881712693843200) (sourceRows 615)) (Integer.Sparse.scale (-35439998022556246425600) (sourceRows 616)) := by decide +kernel

theorem mergedZero613 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged613 x = 0 := by
  rw [mergeCheck613, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck614 : merged614 = Integer.Sparse.merge (Integer.Sparse.scale (-637343203844907738864000) (sourceRows 617)) (Integer.Sparse.scale (678530380446147141561600) (sourceRows 618)) := by decide +kernel

theorem mergedZero614 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged614 x = 0 := by
  rw [mergeCheck614, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck615 : merged615 = Integer.Sparse.merge merged613 merged614 := by decide +kernel

theorem mergedZero615 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged615 x = 0 := by
  rw [mergeCheck615, Integer.Sparse.eval_merge]
  rw [mergedZero613 x h, mergedZero614 x h]
  simp only [add_zero]

theorem mergeCheck616 : merged616 = Integer.Sparse.merge (Integer.Sparse.scale (-1065609150073681940294400) (sourceRows 619)) (Integer.Sparse.scale (-6010686259200) (sourceRows 620)) := by decide +kernel

theorem mergedZero616 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged616 x = 0 := by
  rw [mergeCheck616, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck617 : merged617 = Integer.Sparse.merge (Integer.Sparse.scale (21403041146525765160) (sourceRows 622)) (Integer.Sparse.scale (34846932010389847689600) (sourceRows 623)) := by decide +kernel

theorem mergedZero617 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged617 x = 0 := by
  rw [mergeCheck617, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck618 : merged618 = Integer.Sparse.merge (Integer.Sparse.scale (705912459146564880) (sourceRows 621)) merged617 := by decide +kernel

theorem mergedZero618 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged618 x = 0 := by
  rw [mergeCheck618, Integer.Sparse.eval_merge]
  rw [mergedZero617 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck619 : merged619 = Integer.Sparse.merge merged616 merged618 := by decide +kernel

theorem mergedZero619 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged619 x = 0 := by
  rw [mergeCheck619, Integer.Sparse.eval_merge]
  rw [mergedZero616 x h, mergedZero618 x h]
  simp only [add_zero]

theorem mergeCheck620 : merged620 = Integer.Sparse.merge merged615 merged619 := by decide +kernel

theorem mergedZero620 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged620 x = 0 := by
  rw [mergeCheck620, Integer.Sparse.eval_merge]
  rw [mergedZero615 x h, mergedZero619 x h]
  simp only [add_zero]

theorem mergeCheck621 : merged621 = Integer.Sparse.merge merged612 merged620 := by decide +kernel

theorem mergedZero621 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged621 x = 0 := by
  rw [mergeCheck621, Integer.Sparse.eval_merge]
  rw [mergedZero612 x h, mergedZero620 x h]
  simp only [add_zero]

theorem mergeCheck622 : merged622 = Integer.Sparse.merge (Integer.Sparse.scale (331322077237366359446400) (sourceRows 624)) (Integer.Sparse.scale (-331322077237366359446400) (sourceRows 625)) := by decide +kernel

theorem mergedZero622 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged622 x = 0 := by
  rw [mergeCheck622, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck623 : merged623 = Integer.Sparse.merge (Integer.Sparse.scale (-1273365647698451238086400) (sourceRows 626)) (Integer.Sparse.scale (1726447836523647094300800) (sourceRows 627)) := by decide +kernel

theorem mergedZero623 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged623 x = 0 := by
  rw [mergeCheck623, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck624 : merged624 = Integer.Sparse.merge merged622 merged623 := by decide +kernel

theorem mergedZero624 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged624 x = 0 := by
  rw [mergeCheck624, Integer.Sparse.eval_merge]
  rw [mergedZero622 x h, mergedZero623 x h]
  simp only [add_zero]

theorem mergeCheck625 : merged625 = Integer.Sparse.merge (Integer.Sparse.scale (34106136724371326160) (sourceRows 628)) (Integer.Sparse.scale (1231432543951882757520) (sourceRows 629)) := by decide +kernel

theorem mergedZero625 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged625 x = 0 := by
  rw [mergeCheck625, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck626 : merged626 = Integer.Sparse.merge (Integer.Sparse.scale (-959542896443926158000) (sourceRows 631)) (Integer.Sparse.scale (39036399758274816240) (sourceRows 632)) := by decide +kernel

theorem mergedZero626 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged626 x = 0 := by
  rw [mergeCheck626, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck627 : merged627 = Integer.Sparse.merge (Integer.Sparse.scale (3941989292309040) (sourceRows 630)) merged626 := by decide +kernel

theorem mergedZero627 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged627 x = 0 := by
  rw [mergeCheck627, Integer.Sparse.eval_merge]
  rw [mergedZero626 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck628 : merged628 = Integer.Sparse.merge merged625 merged627 := by decide +kernel

theorem mergedZero628 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged628 x = 0 := by
  rw [mergeCheck628, Integer.Sparse.eval_merge]
  rw [mergedZero625 x h, mergedZero627 x h]
  simp only [add_zero]

theorem mergeCheck629 : merged629 = Integer.Sparse.merge merged624 merged628 := by decide +kernel

theorem mergedZero629 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged629 x = 0 := by
  rw [mergeCheck629, Integer.Sparse.eval_merge]
  rw [mergedZero624 x h, mergedZero628 x h]
  simp only [add_zero]

theorem mergeCheck630 : merged630 = Integer.Sparse.merge (Integer.Sparse.scale (-2089918956130136066880) (sourceRows 633)) (Integer.Sparse.scale (-9171022408576183397113200) (sourceRows 634)) := by decide +kernel

theorem mergedZero630 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged630 x = 0 := by
  rw [mergeCheck630, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck631 : merged631 = Integer.Sparse.merge (Integer.Sparse.scale (-2530375264393200) (sourceRows 636)) (Integer.Sparse.scale (-29306327617414680445065600) (sourceRows 637)) := by decide +kernel

theorem mergedZero631 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged631 x = 0 := by
  rw [mergeCheck631, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck632 : merged632 = Integer.Sparse.merge (Integer.Sparse.scale (-293506470028800) (sourceRows 635)) merged631 := by decide +kernel

theorem mergedZero632 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged632 x = 0 := by
  rw [mergeCheck632, Integer.Sparse.eval_merge]
  rw [mergedZero631 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck633 : merged633 = Integer.Sparse.merge merged630 merged632 := by decide +kernel

theorem mergedZero633 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged633 x = 0 := by
  rw [mergeCheck633, Integer.Sparse.eval_merge]
  rw [mergedZero630 x h, mergedZero632 x h]
  simp only [add_zero]

theorem mergeCheck634 : merged634 = Integer.Sparse.merge (Integer.Sparse.scale (-180806160635086754073600) (sourceRows 638)) (Integer.Sparse.scale (895640525014229533728000) (sourceRows 639)) := by decide +kernel

theorem mergedZero634 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged634 x = 0 := by
  rw [mergeCheck634, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck635 : merged635 = Integer.Sparse.merge (Integer.Sparse.scale (-1101930842966796439833600) (sourceRows 641)) (Integer.Sparse.scale (-57729156710400) (sourceRows 642)) := by decide +kernel

theorem mergedZero635 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged635 x = 0 := by
  rw [mergeCheck635, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck636 : merged636 = Integer.Sparse.merge (Integer.Sparse.scale (630859635326066135270400) (sourceRows 640)) merged635 := by decide +kernel

theorem mergedZero636 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged636 x = 0 := by
  rw [mergeCheck636, Integer.Sparse.eval_merge]
  rw [mergedZero635 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck637 : merged637 = Integer.Sparse.merge merged634 merged636 := by decide +kernel

theorem mergedZero637 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged637 x = 0 := by
  rw [mergeCheck637, Integer.Sparse.eval_merge]
  rw [mergedZero634 x h, mergedZero636 x h]
  simp only [add_zero]

theorem mergeCheck638 : merged638 = Integer.Sparse.merge merged633 merged637 := by decide +kernel

theorem mergedZero638 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged638 x = 0 := by
  rw [mergeCheck638, Integer.Sparse.eval_merge]
  rw [mergedZero633 x h, mergedZero637 x h]
  simp only [add_zero]

theorem mergeCheck639 : merged639 = Integer.Sparse.merge merged629 merged638 := by decide +kernel

theorem mergedZero639 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged639 x = 0 := by
  rw [mergeCheck639, Integer.Sparse.eval_merge]
  rw [mergedZero629 x h, mergedZero638 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck640 : merged640 = Integer.Sparse.merge merged621 merged639 := by decide +kernel

theorem mergedZero640 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged640 x = 0 := by
  rw [mergeCheck640, Integer.Sparse.eval_merge]
  rw [mergedZero621 x h, mergedZero639 x h]
  simp only [add_zero]

theorem mergeCheck641 : merged641 = Integer.Sparse.merge (Integer.Sparse.scale (-5653729723719208320) (sourceRows 643)) (Integer.Sparse.scale (-42806311371270714960) (sourceRows 644)) := by decide +kernel

theorem mergedZero641 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged641 x = 0 := by
  rw [mergeCheck641, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck642 : merged642 = Integer.Sparse.merge (Integer.Sparse.scale (-2468312859423918345350400) (sourceRows 645)) (Integer.Sparse.scale (141759992090224985702400) (sourceRows 646)) := by decide +kernel

theorem mergedZero642 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged642 x = 0 := by
  rw [mergeCheck642, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck643 : merged643 = Integer.Sparse.merge merged641 merged642 := by decide +kernel

theorem mergedZero643 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged643 x = 0 := by
  rw [mergeCheck643, Integer.Sparse.eval_merge]
  rw [mergedZero641 x h, mergedZero642 x h]
  simp only [add_zero]

theorem mergeCheck644 : merged644 = Integer.Sparse.merge (Integer.Sparse.scale (108710420402883689913600) (sourceRows 647)) (Integer.Sparse.scale (-175099373479690752153600) (sourceRows 648)) := by decide +kernel

theorem mergedZero644 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged644 x = 0 := by
  rw [mergeCheck644, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck645 : merged645 = Integer.Sparse.merge (Integer.Sparse.scale (17810357089687619271897600) (sourceRows 650)) (Integer.Sparse.scale (17468391526930000466409600) (sourceRows 651)) := by decide +kernel

theorem mergedZero645 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged645 x = 0 := by
  rw [mergeCheck645, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck646 : merged646 = Integer.Sparse.merge (Integer.Sparse.scale (1261988380800) (sourceRows 649)) merged645 := by decide +kernel

theorem mergedZero646 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged646 x = 0 := by
  rw [mergeCheck646, Integer.Sparse.eval_merge]
  rw [mergedZero645 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck647 : merged647 = Integer.Sparse.merge merged644 merged646 := by decide +kernel

theorem mergedZero647 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged647 x = 0 := by
  rw [mergeCheck647, Integer.Sparse.eval_merge]
  rw [mergedZero644 x h, mergedZero646 x h]
  simp only [add_zero]

theorem mergeCheck648 : merged648 = Integer.Sparse.merge merged643 merged647 := by decide +kernel

theorem mergedZero648 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged648 x = 0 := by
  rw [mergeCheck648, Integer.Sparse.eval_merge]
  rw [mergedZero643 x h, mergedZero647 x h]
  simp only [add_zero]

theorem mergeCheck649 : merged649 = Integer.Sparse.merge (Integer.Sparse.scale (16561630359598220581507200) (sourceRows 652)) (Integer.Sparse.scale (-17625434041647134956915200) (sourceRows 653)) := by decide +kernel

theorem mergedZero649 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged649 x = 0 := by
  rw [mergeCheck649, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck650 : merged650 = Integer.Sparse.merge (Integer.Sparse.scale (-17625434041647134956915200) (sourceRows 655)) (Integer.Sparse.scale (28915758792158895720) (sourceRows 656)) := by decide +kernel

theorem mergedZero650 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged650 x = 0 := by
  rw [mergeCheck650, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck651 : merged651 = Integer.Sparse.merge (Integer.Sparse.scale (12306863618499587266483200) (sourceRows 654)) merged650 := by decide +kernel

theorem mergedZero651 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged651 x = 0 := by
  rw [mergeCheck651, Integer.Sparse.eval_merge]
  rw [mergedZero650 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck652 : merged652 = Integer.Sparse.merge merged649 merged651 := by decide +kernel

theorem mergedZero652 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged652 x = 0 := by
  rw [mergeCheck652, Integer.Sparse.eval_merge]
  rw [mergedZero649 x h, mergedZero651 x h]
  simp only [add_zero]

theorem mergeCheck653 : merged653 = Integer.Sparse.merge (Integer.Sparse.scale (54643242317234425680) (sourceRows 657)) (Integer.Sparse.scale (-44103912558684134100) (sourceRows 658)) := by decide +kernel

theorem mergedZero653 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged653 x = 0 := by
  rw [mergeCheck653, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck654 : merged654 = Integer.Sparse.merge (Integer.Sparse.scale (10219343561617420860) (sourceRows 660)) (Integer.Sparse.scale (-22264931460362354398303200) (sourceRows 661)) := by decide +kernel

theorem mergedZero654 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged654 x = 0 := by
  rw [mergeCheck654, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck655 : merged655 = Integer.Sparse.merge (Integer.Sparse.scale (-307807874520178314240) (sourceRows 659)) merged654 := by decide +kernel

theorem mergedZero655 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged655 x = 0 := by
  rw [mergeCheck655, Integer.Sparse.eval_merge]
  rw [mergedZero654 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck656 : merged656 = Integer.Sparse.merge merged653 merged655 := by decide +kernel

theorem mergedZero656 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged656 x = 0 := by
  rw [mergeCheck656, Integer.Sparse.eval_merge]
  rw [mergedZero653 x h, mergedZero655 x h]
  simp only [add_zero]

theorem mergeCheck657 : merged657 = Integer.Sparse.merge merged652 merged656 := by decide +kernel

theorem mergedZero657 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged657 x = 0 := by
  rw [mergeCheck657, Integer.Sparse.eval_merge]
  rw [mergedZero652 x h, mergedZero656 x h]
  simp only [add_zero]

theorem mergeCheck658 : merged658 = Integer.Sparse.merge merged648 merged657 := by decide +kernel

theorem mergedZero658 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged658 x = 0 := by
  rw [mergeCheck658, Integer.Sparse.eval_merge]
  rw [mergedZero648 x h, mergedZero657 x h]
  simp only [add_zero]

theorem mergeCheck659 : merged659 = Integer.Sparse.merge (Integer.Sparse.scale (-6532381674903690617155200) (sourceRows 662)) (Integer.Sparse.scale (503488327507200) (sourceRows 663)) := by decide +kernel

theorem mergedZero659 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged659 x = 0 := by
  rw [mergeCheck659, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck660 : merged660 = Integer.Sparse.merge (Integer.Sparse.scale (-2349914990335920) (sourceRows 664)) (Integer.Sparse.scale (-743754796142823986572800) (sourceRows 665)) := by decide +kernel

theorem mergedZero660 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged660 x = 0 := by
  rw [mergeCheck660, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck661 : merged661 = Integer.Sparse.merge merged659 merged660 := by decide +kernel

theorem mergedZero661 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged661 x = 0 := by
  rw [mergeCheck661, Integer.Sparse.eval_merge]
  rw [mergedZero659 x h, mergedZero660 x h]
  simp only [add_zero]

theorem mergeCheck662 : merged662 = Integer.Sparse.merge (Integer.Sparse.scale (-115458313420800) (sourceRows 666)) (Integer.Sparse.scale (739071454106002080) (sourceRows 667)) := by decide +kernel

theorem mergedZero662 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged662 x = 0 := by
  rw [mergeCheck662, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck663 : merged663 = Integer.Sparse.merge (Integer.Sparse.scale (28675315742828817972974400) (sourceRows 669)) (Integer.Sparse.scale (-69553469901045950668800) (sourceRows 670)) := by decide +kernel

theorem mergedZero663 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged663 x = 0 := by
  rw [mergeCheck663, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck664 : merged664 = Integer.Sparse.merge (Integer.Sparse.scale (64217467289120904360) (sourceRows 668)) merged663 := by decide +kernel

theorem mergedZero664 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged664 x = 0 := by
  rw [mergeCheck664, Integer.Sparse.eval_merge]
  rw [mergedZero663 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck665 : merged665 = Integer.Sparse.merge merged662 merged664 := by decide +kernel

theorem mergedZero665 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged665 x = 0 := by
  rw [mergeCheck665, Integer.Sparse.eval_merge]
  rw [mergedZero662 x h, mergedZero664 x h]
  simp only [add_zero]

theorem mergeCheck666 : merged666 = Integer.Sparse.merge merged661 merged665 := by decide +kernel

theorem mergedZero666 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged666 x = 0 := by
  rw [mergeCheck666, Integer.Sparse.eval_merge]
  rw [mergedZero661 x h, mergedZero665 x h]
  simp only [add_zero]

theorem mergeCheck667 : merged667 = Integer.Sparse.merge (Integer.Sparse.scale (69553469901045950668800) (sourceRows 671)) (Integer.Sparse.scale (-1076446685649316287801600) (sourceRows 672)) := by decide +kernel

theorem mergedZero667 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged667 x = 0 := by
  rw [mergeCheck667, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck668 : merged668 = Integer.Sparse.merge (Integer.Sparse.scale (903232388859529325587200) (sourceRows 674)) (Integer.Sparse.scale (-1261988380800) (sourceRows 675)) := by decide +kernel

theorem mergedZero668 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged668 x = 0 := by
  rw [mergeCheck668, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck669 : merged669 = Integer.Sparse.merge (Integer.Sparse.scale (567103391807555263046400) (sourceRows 673)) merged668 := by decide +kernel

theorem mergedZero669 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged669 x = 0 := by
  rw [mergeCheck669, Integer.Sparse.eval_merge]
  rw [mergedZero668 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck670 : merged670 = Integer.Sparse.merge merged667 merged669 := by decide +kernel

theorem mergedZero670 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged670 x = 0 := by
  rw [mergeCheck670, Integer.Sparse.eval_merge]
  rw [mergedZero667 x h, mergedZero669 x h]
  simp only [add_zero]

theorem mergeCheck671 : merged671 = Integer.Sparse.merge (Integer.Sparse.scale (-901233837949710963196800) (sourceRows 676)) (Integer.Sparse.scale (-1377888711483183356419200) (sourceRows 677)) := by decide +kernel

theorem mergedZero671 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged671 x = 0 := by
  rw [mergeCheck671, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck672 : merged672 = Integer.Sparse.merge (Integer.Sparse.scale (1063803682048914375408000) (sourceRows 679)) (Integer.Sparse.scale (-3741967058768912799504000) (sourceRows 680)) := by decide +kernel

theorem mergedZero672 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged672 x = 0 := by
  rw [mergeCheck672, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck673 : merged673 = Integer.Sparse.merge (Integer.Sparse.scale (-1063803682048914375408000) (sourceRows 678)) merged672 := by decide +kernel

theorem mergedZero673 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged673 x = 0 := by
  rw [mergeCheck673, Integer.Sparse.eval_merge]
  rw [mergedZero672 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck674 : merged674 = Integer.Sparse.merge merged671 merged673 := by decide +kernel

theorem mergedZero674 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged674 x = 0 := by
  rw [mergeCheck674, Integer.Sparse.eval_merge]
  rw [mergedZero671 x h, mergedZero673 x h]
  simp only [add_zero]

theorem mergeCheck675 : merged675 = Integer.Sparse.merge merged670 merged674 := by decide +kernel

theorem mergedZero675 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged675 x = 0 := by
  rw [mergeCheck675, Integer.Sparse.eval_merge]
  rw [mergedZero670 x h, mergedZero674 x h]
  simp only [add_zero]

theorem mergeCheck676 : merged676 = Integer.Sparse.merge merged666 merged675 := by decide +kernel

theorem mergedZero676 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged676 x = 0 := by
  rw [mergeCheck676, Integer.Sparse.eval_merge]
  rw [mergedZero666 x h, mergedZero675 x h]
  simp only [add_zero]

theorem mergeCheck677 : merged677 = Integer.Sparse.merge merged658 merged676 := by decide +kernel

theorem mergedZero677 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged677 x = 0 := by
  rw [mergeCheck677, Integer.Sparse.eval_merge]
  rw [mergedZero658 x h, mergedZero676 x h]
  simp only [add_zero]

theorem mergeCheck678 : merged678 = Integer.Sparse.merge merged640 merged677 := by decide +kernel

theorem mergedZero678 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged678 x = 0 := by
  rw [mergeCheck678, Integer.Sparse.eval_merge]
  rw [mergedZero640 x h, mergedZero677 x h]
  simp only [add_zero]

theorem mergeCheck679 : merged679 = Integer.Sparse.merge (Integer.Sparse.scale (1063803682048914375408000) (sourceRows 681)) (Integer.Sparse.scale (132470487790378476480) (sourceRows 682)) := by decide +kernel

theorem mergedZero679 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged679 x = 0 := by
  rw [mergeCheck679, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck680 : merged680 = Integer.Sparse.merge (Integer.Sparse.scale (2949156082020556800) (sourceRows 683)) (Integer.Sparse.scale (-19827121709320769817943200) (sourceRows 684)) := by decide +kernel

theorem mergedZero680 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged680 x = 0 := by
  rw [mergeCheck680, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck681 : merged681 = Integer.Sparse.merge merged679 merged680 := by decide +kernel

theorem mergedZero681 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged681 x = 0 := by
  rw [mergeCheck681, Integer.Sparse.eval_merge]
  rw [mergedZero679 x h, mergedZero680 x h]
  simp only [add_zero]

theorem mergeCheck682 : merged682 = Integer.Sparse.merge (Integer.Sparse.scale (511216057374961995504000) (sourceRows 685)) (Integer.Sparse.scale (66677811363355177440) (sourceRows 686)) := by decide +kernel

theorem mergedZero682 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged682 x = 0 := by
  rw [mergeCheck682, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck683 : merged683 = Integer.Sparse.merge (Integer.Sparse.scale (-3530061843853440) (sourceRows 688)) (Integer.Sparse.scale (10413298515183152943261600) (sourceRows 689)) := by decide +kernel

theorem mergedZero683 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged683 x = 0 := by
  rw [mergeCheck683, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck684 : merged684 = Integer.Sparse.merge (Integer.Sparse.scale (-6565420533635242020) (sourceRows 687)) merged683 := by decide +kernel

theorem mergedZero684 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged684 x = 0 := by
  rw [mergeCheck684, Integer.Sparse.eval_merge]
  rw [mergedZero683 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck685 : merged685 = Integer.Sparse.merge merged682 merged684 := by decide +kernel

theorem mergedZero685 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged685 x = 0 := by
  rw [mergeCheck685, Integer.Sparse.eval_merge]
  rw [mergedZero682 x h, mergedZero684 x h]
  simp only [add_zero]

theorem mergeCheck686 : merged686 = Integer.Sparse.merge merged681 merged685 := by decide +kernel

theorem mergedZero686 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged686 x = 0 := by
  rw [mergeCheck686, Integer.Sparse.eval_merge]
  rw [mergedZero681 x h, mergedZero685 x h]
  simp only [add_zero]

theorem mergeCheck687 : merged687 = Integer.Sparse.merge (Integer.Sparse.scale (-175567971090376552060800) (sourceRows 690)) (Integer.Sparse.scale (1541725430375996599507200) (sourceRows 691)) := by decide +kernel

theorem mergedZero687 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged687 x = 0 := by
  rw [mergeCheck687, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck688 : merged688 = Integer.Sparse.merge (Integer.Sparse.scale (-92604421324800) (sourceRows 693)) (Integer.Sparse.scale (-19934244166138119300) (sourceRows 694)) := by decide +kernel

theorem mergedZero688 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged688 x = 0 := by
  rw [mergeCheck688, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck689 : merged689 = Integer.Sparse.merge (Integer.Sparse.scale (-351135942180753104121600) (sourceRows 692)) merged688 := by decide +kernel

theorem mergedZero689 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged689 x = 0 := by
  rw [mergeCheck689, Integer.Sparse.eval_merge]
  rw [mergedZero688 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck690 : merged690 = Integer.Sparse.merge merged687 merged689 := by decide +kernel

theorem mergedZero690 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged690 x = 0 := by
  rw [mergeCheck690, Integer.Sparse.eval_merge]
  rw [mergedZero687 x h, mergedZero689 x h]
  simp only [add_zero]

theorem mergeCheck691 : merged691 = Integer.Sparse.merge (Integer.Sparse.scale (12147001443493221480) (sourceRows 695)) (Integer.Sparse.scale (633572953529726535091200) (sourceRows 696)) := by decide +kernel

theorem mergedZero691 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged691 x = 0 := by
  rw [mergeCheck691, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck692 : merged692 = Integer.Sparse.merge (Integer.Sparse.scale (64594087386683646758400) (sourceRows 698)) (Integer.Sparse.scale (1360543828714150525804800) (sourceRows 699)) := by decide +kernel

theorem mergedZero692 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged692 x = 0 := by
  rw [mergeCheck692, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck693 : merged693 = Integer.Sparse.merge (Integer.Sparse.scale (-70879996045112492851200) (sourceRows 697)) merged692 := by decide +kernel

theorem mergedZero693 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged693 x = 0 := by
  rw [mergeCheck693, Integer.Sparse.eval_merge]
  rw [mergedZero692 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck694 : merged694 = Integer.Sparse.merge merged691 merged693 := by decide +kernel

theorem mergedZero694 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged694 x = 0 := by
  rw [mergeCheck694, Integer.Sparse.eval_merge]
  rw [mergedZero691 x h, mergedZero693 x h]
  simp only [add_zero]

theorem mergeCheck695 : merged695 = Integer.Sparse.merge merged690 merged694 := by decide +kernel

theorem mergedZero695 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged695 x = 0 := by
  rw [mergeCheck695, Integer.Sparse.eval_merge]
  rw [mergedZero690 x h, mergedZero694 x h]
  simp only [add_zero]

theorem mergeCheck696 : merged696 = Integer.Sparse.merge merged686 merged695 := by decide +kernel

theorem mergedZero696 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged696 x = 0 := by
  rw [mergeCheck696, Integer.Sparse.eval_merge]
  rw [mergedZero686 x h, mergedZero695 x h]
  simp only [add_zero]

theorem mergeCheck697 : merged697 = Integer.Sparse.merge (Integer.Sparse.scale (-2523976761600) (sourceRows 700)) (Integer.Sparse.scale (-129379941376760701872000) (sourceRows 701)) := by decide +kernel

theorem mergedZero697 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged697 x = 0 := by
  rw [mergeCheck697, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck698 : merged698 = Integer.Sparse.merge (Integer.Sparse.scale (2708680574095229727100800) (sourceRows 702)) (Integer.Sparse.scale (157042514717134490505600) (sourceRows 703)) := by decide +kernel

theorem mergedZero698 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged698 x = 0 := by
  rw [mergeCheck698, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck699 : merged699 = Integer.Sparse.merge merged697 merged698 := by decide +kernel

theorem mergedZero699 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged699 x = 0 := by
  rw [mergeCheck699, Integer.Sparse.eval_merge]
  rw [mergedZero697 x h, mergedZero698 x h]
  simp only [add_zero]

theorem mergeCheck700 : merged700 = Integer.Sparse.merge (Integer.Sparse.scale (-2780692408357067951107200) (sourceRows 704)) (Integer.Sparse.scale (157042514717134490505600) (sourceRows 705)) := by decide +kernel

theorem mergedZero700 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged700 x = 0 := by
  rw [mergeCheck700, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck701 : merged701 = Integer.Sparse.merge (Integer.Sparse.scale (-1754652205227600) (sourceRows 707)) (Integer.Sparse.scale (-2063922546257510400) (sourceRows 708)) := by decide +kernel

theorem mergedZero701 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged701 x = 0 := by
  rw [mergeCheck701, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck702 : merged702 = Integer.Sparse.merge (Integer.Sparse.scale (-1754652205227600) (sourceRows 706)) merged701 := by decide +kernel

theorem mergedZero702 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged702 x = 0 := by
  rw [mergeCheck702, Integer.Sparse.eval_merge]
  rw [mergedZero701 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck703 : merged703 = Integer.Sparse.merge merged700 merged702 := by decide +kernel

theorem mergedZero703 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged703 x = 0 := by
  rw [mergeCheck703, Integer.Sparse.eval_merge]
  rw [mergedZero700 x h, mergedZero702 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck704 : merged704 = Integer.Sparse.merge merged699 merged703 := by decide +kernel

theorem mergedZero704 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged704 x = 0 := by
  rw [mergeCheck704, Integer.Sparse.eval_merge]
  rw [mergedZero699 x h, mergedZero703 x h]
  simp only [add_zero]

theorem mergeCheck705 : merged705 = Integer.Sparse.merge (Integer.Sparse.scale (-67387812754204225080) (sourceRows 709)) (Integer.Sparse.scale (-43639947341494733040) (sourceRows 710)) := by decide +kernel

theorem mergedZero705 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged705 x = 0 := by
  rw [mergeCheck705, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck706 : merged706 = Integer.Sparse.merge (Integer.Sparse.scale (-64781169078274797120) (sourceRows 712)) (Integer.Sparse.scale (41893774441238814482707200) (sourceRows 713)) := by decide +kernel

theorem mergedZero706 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged706 x = 0 := by
  rw [mergeCheck706, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck707 : merged707 = Integer.Sparse.merge (Integer.Sparse.scale (515659396169742897240) (sourceRows 711)) merged706 := by decide +kernel

theorem mergedZero707 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged707 x = 0 := by
  rw [mergeCheck707, Integer.Sparse.eval_merge]
  rw [mergedZero706 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck708 : merged708 = Integer.Sparse.merge merged705 merged707 := by decide +kernel

theorem mergedZero708 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged708 x = 0 := by
  rw [mergeCheck708, Integer.Sparse.eval_merge]
  rw [mergedZero705 x h, mergedZero707 x h]
  simp only [add_zero]

theorem mergeCheck709 : merged709 = Integer.Sparse.merge (Integer.Sparse.scale (-1219644007896266513164800) (sourceRows 714)) (Integer.Sparse.scale (26525521380906878803200) (sourceRows 715)) := by decide +kernel

theorem mergedZero709 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged709 x = 0 := by
  rw [mergeCheck709, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck710 : merged710 = Integer.Sparse.merge (Integer.Sparse.scale (-15685319416657287600) (sourceRows 717)) (Integer.Sparse.scale (-7810487911277893800) (sourceRows 718)) := by decide +kernel

theorem mergedZero710 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged710 x = 0 := by
  rw [mergeCheck710, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck711 : merged711 = Integer.Sparse.merge (Integer.Sparse.scale (-2016284672045374378502400) (sourceRows 716)) merged710 := by decide +kernel

theorem mergedZero711 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged711 x = 0 := by
  rw [mergeCheck711, Integer.Sparse.eval_merge]
  rw [mergedZero710 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck712 : merged712 = Integer.Sparse.merge merged709 merged711 := by decide +kernel

theorem mergedZero712 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged712 x = 0 := by
  rw [mergeCheck712, Integer.Sparse.eval_merge]
  rw [mergedZero709 x h, mergedZero711 x h]
  simp only [add_zero]

theorem mergeCheck713 : merged713 = Integer.Sparse.merge merged708 merged712 := by decide +kernel

theorem mergedZero713 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged713 x = 0 := by
  rw [mergeCheck713, Integer.Sparse.eval_merge]
  rw [mergedZero708 x h, mergedZero712 x h]
  simp only [add_zero]

theorem mergeCheck714 : merged714 = Integer.Sparse.merge merged704 merged713 := by decide +kernel

theorem mergedZero714 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged714 x = 0 := by
  rw [mergeCheck714, Integer.Sparse.eval_merge]
  rw [mergedZero704 x h, mergedZero713 x h]
  simp only [add_zero]

theorem mergeCheck715 : merged715 = Integer.Sparse.merge merged696 merged714 := by decide +kernel

theorem mergedZero715 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged715 x = 0 := by
  rw [mergeCheck715, Integer.Sparse.eval_merge]
  rw [mergedZero696 x h, mergedZero714 x h]
  simp only [add_zero]

theorem mergeCheck716 : merged716 = Integer.Sparse.merge (Integer.Sparse.scale (-947869633054310400) (sourceRows 719)) (Integer.Sparse.scale (-21481750569788880840) (sourceRows 720)) := by decide +kernel

theorem mergedZero716 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged716 x = 0 := by
  rw [mergeCheck716, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck717 : merged717 = Integer.Sparse.merge (Integer.Sparse.scale (3669935029731532800) (sourceRows 721)) (Integer.Sparse.scale (-285079138638334835760) (sourceRows 722)) := by decide +kernel

theorem mergedZero717 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged717 x = 0 := by
  rw [mergeCheck717, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck718 : merged718 = Integer.Sparse.merge merged716 merged717 := by decide +kernel

theorem mergedZero718 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged718 x = 0 := by
  rw [mergeCheck718, Integer.Sparse.eval_merge]
  rw [mergedZero716 x h, mergedZero717 x h]
  simp only [add_zero]

theorem mergeCheck719 : merged719 = Integer.Sparse.merge (Integer.Sparse.scale (-60546017428297026360) (sourceRows 723)) (Integer.Sparse.scale (161713161009185893632000) (sourceRows 724)) := by decide +kernel

theorem mergedZero719 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged719 x = 0 := by
  rw [mergeCheck719, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck720 : merged720 = Integer.Sparse.merge (Integer.Sparse.scale (-15748880690463733680) (sourceRows 726)) (Integer.Sparse.scale (-497181654194400) (sourceRows 727)) := by decide +kernel

theorem mergedZero720 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged720 x = 0 := by
  rw [mergeCheck720, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck721 : merged721 = Integer.Sparse.merge (Integer.Sparse.scale (711738889540770280089600) (sourceRows 725)) merged720 := by decide +kernel

theorem mergedZero721 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged721 x = 0 := by
  rw [mergeCheck721, Integer.Sparse.eval_merge]
  rw [mergedZero720 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck722 : merged722 = Integer.Sparse.merge merged719 merged721 := by decide +kernel

theorem mergedZero722 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged722 x = 0 := by
  rw [mergeCheck722, Integer.Sparse.eval_merge]
  rw [mergedZero719 x h, mergedZero721 x h]
  simp only [add_zero]

theorem mergeCheck723 : merged723 = Integer.Sparse.merge merged718 merged722 := by decide +kernel

theorem mergedZero723 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged723 x = 0 := by
  rw [mergeCheck723, Integer.Sparse.eval_merge]
  rw [mergedZero718 x h, mergedZero722 x h]
  simp only [add_zero]

theorem mergeCheck724 : merged724 = Integer.Sparse.merge (Integer.Sparse.scale (-31956832956825331380) (sourceRows 728)) (Integer.Sparse.scale (-4620860147565192720) (sourceRows 729)) := by decide +kernel

theorem mergedZero724 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged724 x = 0 := by
  rw [mergeCheck724, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck725 : merged725 = Integer.Sparse.merge (Integer.Sparse.scale (160322844616443283320) (sourceRows 731)) (Integer.Sparse.scale (-15771970071433358580) (sourceRows 732)) := by decide +kernel

theorem mergedZero725 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged725 x = 0 := by
  rw [mergeCheck725, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck726 : merged726 = Integer.Sparse.merge (Integer.Sparse.scale (-10419010210643673660) (sourceRows 730)) merged725 := by decide +kernel

theorem mergedZero726 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged726 x = 0 := by
  rw [mergeCheck726, Integer.Sparse.eval_merge]
  rw [mergedZero725 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck727 : merged727 = Integer.Sparse.merge merged724 merged726 := by decide +kernel

theorem mergedZero727 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged727 x = 0 := by
  rw [mergeCheck727, Integer.Sparse.eval_merge]
  rw [mergedZero724 x h, mergedZero726 x h]
  simp only [add_zero]

theorem mergeCheck728 : merged728 = Integer.Sparse.merge (Integer.Sparse.scale (152119976598860407200) (sourceRows 733)) (Integer.Sparse.scale (29336805401918374080) (sourceRows 734)) := by decide +kernel

theorem mergedZero728 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged728 x = 0 := by
  rw [mergeCheck728, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck729 : merged729 = Integer.Sparse.merge (Integer.Sparse.scale (287705848495532040) (sourceRows 736)) (Integer.Sparse.scale (2551449348425617831800) (sourceRows 737)) := by decide +kernel

theorem mergedZero729 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged729 x = 0 := by
  rw [mergeCheck729, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck730 : merged730 = Integer.Sparse.merge (Integer.Sparse.scale (1143690172873113600) (sourceRows 735)) merged729 := by decide +kernel

theorem mergedZero730 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged730 x = 0 := by
  rw [mergeCheck730, Integer.Sparse.eval_merge]
  rw [mergedZero729 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck731 : merged731 = Integer.Sparse.merge merged728 merged730 := by decide +kernel

theorem mergedZero731 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged731 x = 0 := by
  rw [mergeCheck731, Integer.Sparse.eval_merge]
  rw [mergedZero728 x h, mergedZero730 x h]
  simp only [add_zero]

theorem mergeCheck732 : merged732 = Integer.Sparse.merge merged727 merged731 := by decide +kernel

theorem mergedZero732 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged732 x = 0 := by
  rw [mergeCheck732, Integer.Sparse.eval_merge]
  rw [mergedZero727 x h, mergedZero731 x h]
  simp only [add_zero]

theorem mergeCheck733 : merged733 = Integer.Sparse.merge merged723 merged732 := by decide +kernel

theorem mergedZero733 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged733 x = 0 := by
  rw [mergeCheck733, Integer.Sparse.eval_merge]
  rw [mergedZero723 x h, mergedZero732 x h]
  simp only [add_zero]

theorem mergeCheck734 : merged734 = Integer.Sparse.merge (Integer.Sparse.scale (8169999511792550460) (sourceRows 738)) (Integer.Sparse.scale (-50767565029807039260) (sourceRows 739)) := by decide +kernel

theorem mergedZero734 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged734 x = 0 := by
  rw [mergeCheck734, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck735 : merged735 = Integer.Sparse.merge (Integer.Sparse.scale (107469995504558400) (sourceRows 740)) (Integer.Sparse.scale (425753817945120) (sourceRows 741)) := by decide +kernel

theorem mergedZero735 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged735 x = 0 := by
  rw [mergeCheck735, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck736 : merged736 = Integer.Sparse.merge merged734 merged735 := by decide +kernel

theorem mergedZero736 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged736 x = 0 := by
  rw [mergeCheck736, Integer.Sparse.eval_merge]
  rw [mergedZero734 x h, mergedZero735 x h]
  simp only [add_zero]

theorem mergeCheck737 : merged737 = Integer.Sparse.merge (Integer.Sparse.scale (2250505711964160000) (sourceRows 742)) (Integer.Sparse.scale (11760799978440591120) (sourceRows 743)) := by decide +kernel

theorem mergedZero737 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged737 x = 0 := by
  rw [mergeCheck737, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck738 : merged738 = Integer.Sparse.merge (Integer.Sparse.scale (32677948302505964640) (sourceRows 745)) (Integer.Sparse.scale (-10519567825086374460) (sourceRows 746)) := by decide +kernel

theorem mergedZero738 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged738 x = 0 := by
  rw [mergeCheck738, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck739 : merged739 = Integer.Sparse.merge (Integer.Sparse.scale (110266353298757584051200) (sourceRows 744)) merged738 := by decide +kernel

theorem mergedZero739 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged739 x = 0 := by
  rw [mergeCheck739, Integer.Sparse.eval_merge]
  rw [mergedZero738 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck740 : merged740 = Integer.Sparse.merge merged737 merged739 := by decide +kernel

theorem mergedZero740 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged740 x = 0 := by
  rw [mergeCheck740, Integer.Sparse.eval_merge]
  rw [mergedZero737 x h, mergedZero739 x h]
  simp only [add_zero]

theorem mergeCheck741 : merged741 = Integer.Sparse.merge merged736 merged740 := by decide +kernel

theorem mergedZero741 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged741 x = 0 := by
  rw [mergeCheck741, Integer.Sparse.eval_merge]
  rw [mergedZero736 x h, mergedZero740 x h]
  simp only [add_zero]

theorem mergeCheck742 : merged742 = Integer.Sparse.merge (Integer.Sparse.scale (-25477210563962940300) (sourceRows 747)) (Integer.Sparse.scale (-4308944702388527040) (sourceRows 748)) := by decide +kernel

theorem mergedZero742 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged742 x = 0 := by
  rw [mergeCheck742, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck743 : merged743 = Integer.Sparse.merge (Integer.Sparse.scale (2200590057418776220680) (sourceRows 750)) (Integer.Sparse.scale (409886526510720) (sourceRows 751)) := by decide +kernel

theorem mergedZero743 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged743 x = 0 := by
  rw [mergeCheck743, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck744 : merged744 = Integer.Sparse.merge (Integer.Sparse.scale (18533517591623670720) (sourceRows 749)) merged743 := by decide +kernel

theorem mergedZero744 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged744 x = 0 := by
  rw [mergeCheck744, Integer.Sparse.eval_merge]
  rw [mergedZero743 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck745 : merged745 = Integer.Sparse.merge merged742 merged744 := by decide +kernel

theorem mergedZero745 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged745 x = 0 := by
  rw [mergeCheck745, Integer.Sparse.eval_merge]
  rw [mergedZero742 x h, mergedZero744 x h]
  simp only [add_zero]

theorem mergeCheck746 : merged746 = Integer.Sparse.merge (Integer.Sparse.scale (-1413167226266271887107200) (sourceRows 752)) (Integer.Sparse.scale (1866666641580049315910400) (sourceRows 753)) := by decide +kernel

theorem mergedZero746 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged746 x = 0 := by
  rw [mergeCheck746, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck747 : merged747 = Integer.Sparse.merge (Integer.Sparse.scale (1866666641580049315910400) (sourceRows 755)) (Integer.Sparse.scale (-933333320790024657955200) (sourceRows 756)) := by decide +kernel

theorem mergedZero747 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged747 x = 0 := by
  rw [mergeCheck747, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck748 : merged748 = Integer.Sparse.merge (Integer.Sparse.scale (894953844220330439596800) (sourceRows 754)) merged747 := by decide +kernel

theorem mergedZero748 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged748 x = 0 := by
  rw [mergeCheck748, Integer.Sparse.eval_merge]
  rw [mergedZero747 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck749 : merged749 = Integer.Sparse.merge merged746 merged748 := by decide +kernel

theorem mergedZero749 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged749 x = 0 := by
  rw [mergeCheck749, Integer.Sparse.eval_merge]
  rw [mergedZero746 x h, mergedZero748 x h]
  simp only [add_zero]

theorem mergeCheck750 : merged750 = Integer.Sparse.merge merged745 merged749 := by decide +kernel

theorem mergedZero750 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged750 x = 0 := by
  rw [mergeCheck750, Integer.Sparse.eval_merge]
  rw [mergedZero745 x h, mergedZero749 x h]
  simp only [add_zero]

theorem mergeCheck751 : merged751 = Integer.Sparse.merge merged741 merged750 := by decide +kernel

theorem mergedZero751 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged751 x = 0 := by
  rw [mergeCheck751, Integer.Sparse.eval_merge]
  rw [mergedZero741 x h, mergedZero750 x h]
  simp only [add_zero]

theorem mergeCheck752 : merged752 = Integer.Sparse.merge merged733 merged751 := by decide +kernel

theorem mergedZero752 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged752 x = 0 := by
  rw [mergeCheck752, Integer.Sparse.eval_merge]
  rw [mergedZero733 x h, mergedZero751 x h]
  simp only [add_zero]

theorem mergeCheck753 : merged753 = Integer.Sparse.merge merged715 merged752 := by decide +kernel

theorem mergedZero753 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged753 x = 0 := by
  rw [mergeCheck753, Integer.Sparse.eval_merge]
  rw [mergedZero715 x h, mergedZero752 x h]
  simp only [add_zero]

theorem mergeCheck754 : merged754 = Integer.Sparse.merge merged678 merged753 := by decide +kernel

theorem mergedZero754_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged754 x = 0 := by
  rw [mergeCheck754, Integer.Sparse.eval_merge]
  rw [mergedZero678 x h, mergedZero753 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero754_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero754_e_oai
