-- Prove2me | solution 1 for GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:25.784853+00:00
-- url     : https://prove2.me/submissions/d0ae9d2b-fc54-410e-b6ac-ba271d3f0cd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Theorems.Thm_GlobalTheory_SummableExpNegAbsSum_summable_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableExpNegAbsSum
namespace GlobalTheory.SummableExpNegAbsSum
theorem _root_.solution {ι : Type} [inst : Fintype ι] :
    Summable fun (m : ι → ℤ) ↦ Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) := by
  classical
  set g : ℤ → ℝ := fun n ↦ Real.exp (-|(n : ℝ)|) with hg
  have hgpos : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hgs : Summable g := summable_int
  have hprod : ∀ m : ι → ℤ, Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) = ∏ i : ι, g (m i) := by
    intro m
    simp only [hg]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simp_rw [hprod]
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' n : ℤ, g n)
    (fun m => Finset.prod_nonneg fun i _ => hgpos _) fun s => ?_
  set T : ι → Finset ℤ := fun i => s.image (fun m : ι → ℤ => m i) with hT
  have hsub : s ⊆ Fintype.piFinset T := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hm
  calc ∑ m ∈ s, ∏ i : ι, g (m i)
      ≤ ∑ m ∈ Fintype.piFinset T, ∏ i : ι, g (m i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun i _ => hgpos _
    _ = ∏ i : ι, ∑ n ∈ T i, g n := (Finset.prod_univ_sum T (fun _ n => g n)).symm
    _ ≤ ∏ _i : ι, ∑' n : ℤ, g n := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => hgpos _)
          fun i _ => ?_
        exact hgs.sum_le_tsum _ fun _ _ => hgpos _
end GlobalTheory.SummableExpNegAbsSum
