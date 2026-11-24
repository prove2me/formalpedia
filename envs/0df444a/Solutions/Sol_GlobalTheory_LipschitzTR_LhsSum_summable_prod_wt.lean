-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.summable_prod_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:00:43.735918+00:00
-- url     : https://prove2.me/submissions/141eb34f-34c1-46f9-9ad1-e98e2b6d8958

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_wt_nonneg
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_summable_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR.LhsSum
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι] :
    Summable (fun n : ι → ℤ => ∏ i, wt (n i)) := by
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' m, wt m)
    (fun n => Finset.prod_nonneg fun i _ => wt_nonneg _) (fun u => ?_)
  calc ∑ n ∈ u, ∏ i, wt (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : ι → ℤ => n i)), ∏ i, wt (n i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_image_of_mem _ hn
        · intro n _ _
          exact Finset.prod_nonneg fun i _ => wt_nonneg _
    _ = ∏ i, ∑ m ∈ u.image (fun n : ι → ℤ => n i), wt m := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' m, wt m := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg fun m _ => wt_nonneg m
        · intro i _; exact summable_wt.sum_le_tsum _ (fun m _ => wt_nonneg m)
end GlobalTheory.LipschitzTR.LhsSum
