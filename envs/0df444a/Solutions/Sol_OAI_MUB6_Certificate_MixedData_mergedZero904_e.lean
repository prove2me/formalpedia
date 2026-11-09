-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedData.mergedZero904_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:29:29.670472+00:00
-- url     : https://prove2.me/submissions/426abaf3-e58e-420d-acab-7be727946dc1

import Mathlib
import Definitions.Def_OAIQ106E196
import Definitions.Def_OAIQ106E185
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck830 : merged830 = Integer.Sparse.merge (Integer.Sparse.scale (-1155245683304160) (sourceRows 833)) (Integer.Sparse.scale (-97835490009600) (sourceRows 834)) := by decide +kernel

theorem mergedZero830 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged830 x = 0 := by
  rw [mergeCheck830, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck831 : merged831 = Integer.Sparse.merge (Integer.Sparse.scale (-1674594961515657076896000) (sourceRows 835)) (Integer.Sparse.scale (-11570276478347596800) (sourceRows 836)) := by decide +kernel

theorem mergedZero831 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged831 x = 0 := by
  rw [mergeCheck831, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck832 : merged832 = Integer.Sparse.merge merged830 merged831 := by decide +kernel

theorem mergedZero832 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged832 x = 0 := by
  rw [mergeCheck832, Integer.Sparse.eval_merge]
  rw [mergedZero830 x h, mergedZero831 x h]
  simp only [add_zero]

theorem mergeCheck833 : merged833 = Integer.Sparse.merge (Integer.Sparse.scale (2059744869981382449801600) (sourceRows 837)) (Integer.Sparse.scale (921136252608188033356800) (sourceRows 838)) := by decide +kernel

theorem mergedZero833 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged833 x = 0 := by
  rw [mergeCheck833, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck834 : merged834 = Integer.Sparse.merge (Integer.Sparse.scale (42287982836399769840) (sourceRows 840)) (Integer.Sparse.scale (450267984579108379110) (sourceRows 841)) := by decide +kernel

theorem mergedZero834 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged834 x = 0 := by
  rw [mergeCheck834, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck835 : merged835 = Integer.Sparse.merge (Integer.Sparse.scale (-2084483546337268237996800) (sourceRows 839)) merged834 := by decide +kernel

theorem mergedZero835 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged835 x = 0 := by
  rw [mergeCheck835, Integer.Sparse.eval_merge]
  rw [mergedZero834 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck836 : merged836 = Integer.Sparse.merge merged833 merged835 := by decide +kernel

theorem mergedZero836 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged836 x = 0 := by
  rw [mergeCheck836, Integer.Sparse.eval_merge]
  rw [mergedZero833 x h, mergedZero835 x h]
  simp only [add_zero]

theorem mergeCheck837 : merged837 = Integer.Sparse.merge merged832 merged836 := by decide +kernel

theorem mergedZero837 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged837 x = 0 := by
  rw [mergeCheck837, Integer.Sparse.eval_merge]
  rw [mergedZero832 x h, mergedZero836 x h]
  simp only [add_zero]

theorem mergeCheck838 : merged838 = Integer.Sparse.merge (Integer.Sparse.scale (22566536911657184460) (sourceRows 842)) (Integer.Sparse.scale (-44813014737417380160) (sourceRows 843)) := by decide +kernel

theorem mergedZero838 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged838 x = 0 := by
  rw [mergeCheck838, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck839 : merged839 = Integer.Sparse.merge (Integer.Sparse.scale (47566172352105513960) (sourceRows 845)) (Integer.Sparse.scale (1790802657719793379670400) (sourceRows 846)) := by decide +kernel

theorem mergedZero839 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged839 x = 0 := by
  rw [mergeCheck839, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck840 : merged840 = Integer.Sparse.merge (Integer.Sparse.scale (265840311653398986420) (sourceRows 844)) merged839 := by decide +kernel

theorem mergedZero840 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged840 x = 0 := by
  rw [mergeCheck840, Integer.Sparse.eval_merge]
  rw [mergedZero839 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck841 : merged841 = Integer.Sparse.merge merged838 merged840 := by decide +kernel

theorem mergedZero841 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged841 x = 0 := by
  rw [mergeCheck841, Integer.Sparse.eval_merge]
  rw [mergedZero838 x h, mergedZero840 x h]
  simp only [add_zero]

theorem mergeCheck842 : merged842 = Integer.Sparse.merge (Integer.Sparse.scale (-25125394117320) (sourceRows 847)) (Integer.Sparse.scale (-184923048040484314982400) (sourceRows 848)) := by decide +kernel

theorem mergedZero842 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged842 x = 0 := by
  rw [mergeCheck842, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck843 : merged843 = Integer.Sparse.merge (Integer.Sparse.scale (-2469412182638301297868800) (sourceRows 850)) (Integer.Sparse.scale (-57729156710400) (sourceRows 851)) := by decide +kernel

theorem mergedZero843 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged843 x = 0 := by
  rw [mergeCheck843, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck844 : merged844 = Integer.Sparse.merge (Integer.Sparse.scale (2768195092127991949785600) (sourceRows 849)) merged843 := by decide +kernel

theorem mergedZero844 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged844 x = 0 := by
  rw [mergeCheck844, Integer.Sparse.eval_merge]
  rw [mergedZero843 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck845 : merged845 = Integer.Sparse.merge merged842 merged844 := by decide +kernel

theorem mergedZero845 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged845 x = 0 := by
  rw [mergeCheck845, Integer.Sparse.eval_merge]
  rw [mergedZero842 x h, mergedZero844 x h]
  simp only [add_zero]

theorem mergeCheck846 : merged846 = Integer.Sparse.merge merged841 merged845 := by decide +kernel

theorem mergedZero846 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged846 x = 0 := by
  rw [mergeCheck846, Integer.Sparse.eval_merge]
  rw [mergedZero841 x h, mergedZero845 x h]
  simp only [add_zero]

theorem mergeCheck847 : merged847 = Integer.Sparse.merge merged837 merged846 := by decide +kernel

theorem mergedZero847 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged847 x = 0 := by
  rw [mergeCheck847, Integer.Sparse.eval_merge]
  rw [mergedZero837 x h, mergedZero846 x h]
  simp only [add_zero]

theorem mergeCheck848 : merged848 = Integer.Sparse.merge (Integer.Sparse.scale (-21404036205045443880) (sourceRows 852)) (Integer.Sparse.scale (-1884576574573069440) (sourceRows 853)) := by decide +kernel

theorem mergedZero848 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged848 x = 0 := by
  rw [mergeCheck848, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck849 : merged849 = Integer.Sparse.merge (Integer.Sparse.scale (210954940378932347942400) (sourceRows 854)) (Integer.Sparse.scale (-4303698666462427966675200) (sourceRows 855)) := by decide +kernel

theorem mergedZero849 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged849 x = 0 := by
  rw [mergeCheck849, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck850 : merged850 = Integer.Sparse.merge merged848 merged849 := by decide +kernel

theorem mergedZero850 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged850 x = 0 := by
  rw [mergeCheck850, Integer.Sparse.eval_merge]
  rw [mergedZero848 x h, mergedZero849 x h]
  simp only [add_zero]

theorem mergeCheck851 : merged851 = Integer.Sparse.merge (Integer.Sparse.scale (368536028691644527392000) (sourceRows 856)) (Integer.Sparse.scale (57729156710400) (sourceRows 857)) := by decide +kernel

theorem mergedZero851 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged851 x = 0 := by
  rw [mergeCheck851, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck852 : merged852 = Integer.Sparse.merge (Integer.Sparse.scale (-32108733644560452180) (sourceRows 859)) (Integer.Sparse.scale (-147310029334970240659200) (sourceRows 860)) := by decide +kernel

theorem mergedZero852 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged852 x = 0 := by
  rw [mergeCheck852, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck853 : merged853 = Integer.Sparse.merge (Integer.Sparse.scale (-1478636285801393040) (sourceRows 858)) merged852 := by decide +kernel

theorem mergedZero853 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged853 x = 0 := by
  rw [mergeCheck853, Integer.Sparse.eval_merge]
  rw [mergedZero852 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck854 : merged854 = Integer.Sparse.merge merged851 merged853 := by decide +kernel

theorem mergedZero854 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged854 x = 0 := by
  rw [mergeCheck854, Integer.Sparse.eval_merge]
  rw [mergedZero851 x h, mergedZero853 x h]
  simp only [add_zero]

theorem mergeCheck855 : merged855 = Integer.Sparse.merge merged850 merged854 := by decide +kernel

theorem mergedZero855 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged855 x = 0 := by
  rw [mergeCheck855, Integer.Sparse.eval_merge]
  rw [mergedZero850 x h, mergedZero854 x h]
  simp only [add_zero]

theorem mergeCheck856 : merged856 = Integer.Sparse.merge (Integer.Sparse.scale (1076446685649316287801600) (sourceRows 861)) (Integer.Sparse.scale (157975055605739686406400) (sourceRows 862)) := by decide +kernel

theorem mergedZero856 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged856 x = 0 := by
  rw [mergeCheck856, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck857 : merged857 = Integer.Sparse.merge (Integer.Sparse.scale (692708980276904540040) (sourceRows 864)) (Integer.Sparse.scale (84487198621535320800) (sourceRows 865)) := by decide +kernel

theorem mergedZero857 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged857 x = 0 := by
  rw [mergeCheck857, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck858 : merged858 = Integer.Sparse.merge (Integer.Sparse.scale (-512474857865320423500) (sourceRows 863)) merged857 := by decide +kernel

theorem mergedZero858 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged858 x = 0 := by
  rw [mergeCheck858, Integer.Sparse.eval_merge]
  rw [mergedZero857 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck859 : merged859 = Integer.Sparse.merge merged856 merged858 := by decide +kernel

theorem mergedZero859 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged859 x = 0 := by
  rw [mergeCheck859, Integer.Sparse.eval_merge]
  rw [mergedZero856 x h, mergedZero858 x h]
  simp only [add_zero]

theorem mergeCheck860 : merged860 = Integer.Sparse.merge (Integer.Sparse.scale (-190310428686927084480) (sourceRows 866)) (Integer.Sparse.scale (-38869338593082158280) (sourceRows 867)) := by decide +kernel

theorem mergedZero860 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged860 x = 0 := by
  rw [mergeCheck860, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck861 : merged861 = Integer.Sparse.merge (Integer.Sparse.scale (-87238864064785392691200) (sourceRows 869)) (Integer.Sparse.scale (2410734958947838049587200) (sourceRows 870)) := by decide +kernel

theorem mergedZero861 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged861 x = 0 := by
  rw [mergeCheck861, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck862 : merged862 = Integer.Sparse.merge (Integer.Sparse.scale (-2577803163888960) (sourceRows 868)) merged861 := by decide +kernel

theorem mergedZero862 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged862 x = 0 := by
  rw [mergeCheck862, Integer.Sparse.eval_merge]
  rw [mergedZero861 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck863 : merged863 = Integer.Sparse.merge merged860 merged862 := by decide +kernel

theorem mergedZero863 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged863 x = 0 := by
  rw [mergeCheck863, Integer.Sparse.eval_merge]
  rw [mergedZero860 x h, mergedZero862 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck864 : merged864 = Integer.Sparse.merge merged859 merged863 := by decide +kernel

theorem mergedZero864 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged864 x = 0 := by
  rw [mergeCheck864, Integer.Sparse.eval_merge]
  rw [mergedZero859 x h, mergedZero863 x h]
  simp only [add_zero]

theorem mergeCheck865 : merged865 = Integer.Sparse.merge merged855 merged864 := by decide +kernel

theorem mergedZero865 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged865 x = 0 := by
  rw [mergeCheck865, Integer.Sparse.eval_merge]
  rw [mergedZero855 x h, mergedZero864 x h]
  simp only [add_zero]

theorem mergeCheck866 : merged866 = Integer.Sparse.merge merged847 merged865 := by decide +kernel

theorem mergedZero866 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged866 x = 0 := by
  rw [mergeCheck866, Integer.Sparse.eval_merge]
  rw [mergedZero847 x h, mergedZero865 x h]
  simp only [add_zero]

theorem mergeCheck867 : merged867 = Integer.Sparse.merge (Integer.Sparse.scale (-72128235110400) (sourceRows 871)) (Integer.Sparse.scale (-3567273254095581660) (sourceRows 872)) := by decide +kernel

theorem mergedZero867 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged867 x = 0 := by
  rw [mergeCheck867, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck868 : merged868 = Integer.Sparse.merge (Integer.Sparse.scale (-1906487626864356480) (sourceRows 873)) (Integer.Sparse.scale (-263560784863440952339200) (sourceRows 874)) := by decide +kernel

theorem mergedZero868 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged868 x = 0 := by
  rw [mergeCheck868, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck869 : merged869 = Integer.Sparse.merge merged867 merged868 := by decide +kernel

theorem mergedZero869 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged869 x = 0 := by
  rw [mergeCheck869, Integer.Sparse.eval_merge]
  rw [mergedZero867 x h, mergedZero868 x h]
  simp only [add_zero]

theorem mergeCheck870 : merged870 = Integer.Sparse.merge (Integer.Sparse.scale (-3972563603947462167705600) (sourceRows 875)) (Integer.Sparse.scale (311259110308597177171200) (sourceRows 876)) := by decide +kernel

theorem mergedZero870 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged870 x = 0 := by
  rw [mergeCheck870, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck871 : merged871 = Integer.Sparse.merge (Integer.Sparse.scale (146753235014400) (sourceRows 878)) (Integer.Sparse.scale (66432946601402374694400) (sourceRows 879)) := by decide +kernel

theorem mergedZero871 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged871 x = 0 := by
  rw [mergeCheck871, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck872 : merged872 = Integer.Sparse.merge (Integer.Sparse.scale (632593816098300) (sourceRows 877)) merged871 := by decide +kernel

theorem mergedZero872 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged872 x = 0 := by
  rw [mergeCheck872, Integer.Sparse.eval_merge]
  rw [mergedZero871 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck873 : merged873 = Integer.Sparse.merge merged870 merged872 := by decide +kernel

theorem mergedZero873 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged873 x = 0 := by
  rw [mergeCheck873, Integer.Sparse.eval_merge]
  rw [mergedZero870 x h, mergedZero872 x h]
  simp only [add_zero]

theorem mergeCheck874 : merged874 = Integer.Sparse.merge merged869 merged873 := by decide +kernel

theorem mergedZero874 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged874 x = 0 := by
  rw [mergeCheck874, Integer.Sparse.eval_merge]
  rw [mergedZero869 x h, mergedZero873 x h]
  simp only [add_zero]

theorem mergeCheck875 : merged875 = Integer.Sparse.merge (Integer.Sparse.scale (-921124682331709685760000) (sourceRows 880)) (Integer.Sparse.scale (819773053021440) (sourceRows 881)) := by decide +kernel

theorem mergedZero875 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged875 x = 0 := by
  rw [mergeCheck875, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck876 : merged876 = Integer.Sparse.merge (Integer.Sparse.scale (53546743206027198120) (sourceRows 883)) (Integer.Sparse.scale (-219486183902402356800) (sourceRows 884)) := by decide +kernel

theorem mergedZero876 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged876 x = 0 := by
  rw [mergeCheck876, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck877 : merged877 = Integer.Sparse.merge (Integer.Sparse.scale (29556359334619776120) (sourceRows 882)) merged876 := by decide +kernel

theorem mergedZero877 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged877 x = 0 := by
  rw [mergeCheck877, Integer.Sparse.eval_merge]
  rw [mergedZero876 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck878 : merged878 = Integer.Sparse.merge merged875 merged877 := by decide +kernel

theorem mergedZero878 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged878 x = 0 := by
  rw [mergeCheck878, Integer.Sparse.eval_merge]
  rw [mergedZero875 x h, mergedZero877 x h]
  simp only [add_zero]

theorem mergeCheck879 : merged879 = Integer.Sparse.merge (Integer.Sparse.scale (242402499349324494600) (sourceRows 885)) (Integer.Sparse.scale (72128235110400) (sourceRows 886)) := by decide +kernel

theorem mergedZero879 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged879 x = 0 := by
  rw [mergeCheck879, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck880 : merged880 = Integer.Sparse.merge (Integer.Sparse.scale (2860217727077995200) (sourceRows 888)) (Integer.Sparse.scale (-49242922471215855648000) (sourceRows 889)) := by decide +kernel

theorem mergedZero880 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged880 x = 0 := by
  rw [mergeCheck880, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck881 : merged881 = Integer.Sparse.merge (Integer.Sparse.scale (3567224336350576860) (sourceRows 887)) merged880 := by decide +kernel

theorem mergedZero881 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged881 x = 0 := by
  rw [mergeCheck881, Integer.Sparse.eval_merge]
  rw [mergedZero880 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck882 : merged882 = Integer.Sparse.merge merged879 merged881 := by decide +kernel

theorem mergedZero882 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged882 x = 0 := by
  rw [mergeCheck882, Integer.Sparse.eval_merge]
  rw [mergedZero879 x h, mergedZero881 x h]
  simp only [add_zero]

theorem mergeCheck883 : merged883 = Integer.Sparse.merge merged878 merged882 := by decide +kernel

theorem mergedZero883 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged883 x = 0 := by
  rw [mergeCheck883, Integer.Sparse.eval_merge]
  rw [mergedZero878 x h, mergedZero882 x h]
  simp only [add_zero]

theorem mergeCheck884 : merged884 = Integer.Sparse.merge merged874 merged883 := by decide +kernel

theorem mergedZero884 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged884 x = 0 := by
  rw [mergeCheck884, Integer.Sparse.eval_merge]
  rw [mergedZero874 x h, mergedZero883 x h]
  simp only [add_zero]

theorem mergeCheck885 : merged885 = Integer.Sparse.merge (Integer.Sparse.scale (72128235110400) (sourceRows 890)) (Integer.Sparse.scale (953243813432178240) (sourceRows 891)) := by decide +kernel

theorem mergedZero885 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged885 x = 0 := by
  rw [mergeCheck885, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck886 : merged886 = Integer.Sparse.merge (Integer.Sparse.scale (3567273254095581660) (sourceRows 892)) (Integer.Sparse.scale (-211444784033093236483200) (sourceRows 893)) := by decide +kernel

theorem mergedZero886 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged886 x = 0 := by
  rw [mergeCheck886, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck887 : merged887 = Integer.Sparse.merge merged885 merged886 := by decide +kernel

theorem mergedZero887 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged887 x = 0 := by
  rw [mergeCheck887, Integer.Sparse.eval_merge]
  rw [mergedZero885 x h, mergedZero886 x h]
  simp only [add_zero]

theorem mergeCheck888 : merged888 = Integer.Sparse.merge (Integer.Sparse.scale (1314026976061800) (sourceRows 894)) (Integer.Sparse.scale (-585998525561732615606400) (sourceRows 895)) := by decide +kernel

theorem mergedZero888 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged888 x = 0 := by
  rw [mergeCheck888, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck889 : merged889 = Integer.Sparse.merge (Integer.Sparse.scale (-39930357866962993080) (sourceRows 897)) (Integer.Sparse.scale (15402254644109338320) (sourceRows 898)) := by decide +kernel

theorem mergedZero889 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged889 x = 0 := by
  rw [mergeCheck889, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck890 : merged890 = Integer.Sparse.merge (Integer.Sparse.scale (-418503175372800) (sourceRows 896)) merged889 := by decide +kernel

theorem mergedZero890 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged890 x = 0 := by
  rw [mergeCheck890, Integer.Sparse.eval_merge]
  rw [mergedZero889 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck891 : merged891 = Integer.Sparse.merge merged888 merged890 := by decide +kernel

theorem mergedZero891 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged891 x = 0 := by
  rw [mergeCheck891, Integer.Sparse.eval_merge]
  rw [mergedZero888 x h, mergedZero890 x h]
  simp only [add_zero]

theorem mergeCheck892 : merged892 = Integer.Sparse.merge merged887 merged891 := by decide +kernel

theorem mergedZero892 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged892 x = 0 := by
  rw [mergeCheck892, Integer.Sparse.eval_merge]
  rw [mergedZero887 x h, mergedZero891 x h]
  simp only [add_zero]

theorem mergeCheck893 : merged893 = Integer.Sparse.merge (Integer.Sparse.scale (1475447810832204249600) (sourceRows 899)) (Integer.Sparse.scale (22725254893551897960) (sourceRows 900)) := by decide +kernel

theorem mergedZero893 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged893 x = 0 := by
  rw [mergeCheck893, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck894 : merged894 = Integer.Sparse.merge (Integer.Sparse.scale (-50247218510111988120) (sourceRows 902)) (Integer.Sparse.scale (-28911139329485030520) (sourceRows 903)) := by decide +kernel

theorem mergedZero894 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged894 x = 0 := by
  rw [mergeCheck894, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck895 : merged895 = Integer.Sparse.merge (Integer.Sparse.scale (-26256384453549081720) (sourceRows 901)) merged894 := by decide +kernel

theorem mergedZero895 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged895 x = 0 := by
  rw [mergeCheck895, Integer.Sparse.eval_merge]
  rw [mergedZero894 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMerge_Block28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergeCheck896 : merged896 = Integer.Sparse.merge merged893 merged895 := by decide +kernel

theorem mergedZero896 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged896 x = 0 := by
  rw [mergeCheck896, Integer.Sparse.eval_merge]
  rw [mergedZero893 x h, mergedZero895 x h]
  simp only [add_zero]

theorem mergeCheck897 : merged897 = Integer.Sparse.merge (Integer.Sparse.scale (-52898435787043577640) (sourceRows 904)) (Integer.Sparse.scale (-1006969873725849600) (sourceRows 905)) := by decide +kernel

theorem mergedZero897 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged897 x = 0 := by
  rw [mergeCheck897, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck898 : merged898 = Integer.Sparse.merge (Integer.Sparse.scale (184930655728187461478400) (sourceRows 907)) (Integer.Sparse.scale (5251582620729523680) (sourceRows 908)) := by decide +kernel

theorem mergedZero898 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged898 x = 0 := by
  rw [mergeCheck898, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck899 : merged899 = Integer.Sparse.merge (Integer.Sparse.scale (-3078503722419168960) (sourceRows 906)) merged898 := by decide +kernel

theorem mergedZero899 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged899 x = 0 := by
  rw [mergeCheck899, Integer.Sparse.eval_merge]
  rw [mergedZero898 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

theorem mergeCheck900 : merged900 = Integer.Sparse.merge merged897 merged899 := by decide +kernel

theorem mergedZero900 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged900 x = 0 := by
  rw [mergeCheck900, Integer.Sparse.eval_merge]
  rw [mergedZero897 x h, mergedZero899 x h]
  simp only [add_zero]

theorem mergeCheck901 : merged901 = Integer.Sparse.merge merged896 merged900 := by decide +kernel

theorem mergedZero901 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged901 x = 0 := by
  rw [mergeCheck901, Integer.Sparse.eval_merge]
  rw [mergedZero896 x h, mergedZero900 x h]
  simp only [add_zero]

theorem mergeCheck902 : merged902 = Integer.Sparse.merge merged892 merged901 := by decide +kernel

theorem mergedZero902 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged902 x = 0 := by
  rw [mergeCheck902, Integer.Sparse.eval_merge]
  rw [mergedZero892 x h, mergedZero901 x h]
  simp only [add_zero]

theorem mergeCheck903 : merged903 = Integer.Sparse.merge merged884 merged902 := by decide +kernel

theorem mergedZero903 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged903 x = 0 := by
  rw [mergeCheck903, Integer.Sparse.eval_merge]
  rw [mergedZero884 x h, mergedZero902 x h]
  simp only [add_zero]

theorem mergeCheck904 : merged904 = Integer.Sparse.merge merged866 merged903 := by decide +kernel

theorem mergedZero904_e_oai (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged904 x = 0 := by
  rw [mergeCheck904, Integer.Sparse.eval_merge]
  rw [mergedZero866 x h, mergedZero903 x h]
  simp only [add_zero]

end MUB6.Certificate.MixedData

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedData.mergedZero904_e_oai := @OAI.MUB6.Certificate.MixedData.mergedZero904_e_oai
