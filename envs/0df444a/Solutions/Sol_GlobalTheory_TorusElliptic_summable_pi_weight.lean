-- Prove2me | solution 1 for GlobalTheory.TorusElliptic.summable_pi_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:19.68092+00:00
-- url     : https://prove2.me/submissions/706876fd-2f33-4b3a-b89f-4f672df194ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRapidFourierSeriesOfIntPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorusEllipticSystemSolvable
import Theorems.Thm_GlobalTheory_TorusElliptic_summable_int_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.TorusElliptic
namespace GlobalTheory.TorusElliptic
theorem _root_.solution (n : ℕ) :
    Summable (fun ν : Fin n → ℤ => ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2) := by
  classical
  refine summable_of_sum_le (c := ∏ _k : Fin n, ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)
    (fun ν => by positivity) fun s => ?_
  calc ∑ ν ∈ s, ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2
      ≤ ∑ ν ∈ Fintype.piFinset (fun k => (s.image (fun ν => ν k) : Finset ℤ)),
          ∏ k, 1 / (1 + |(ν k : ℝ)|) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun ν hν => ?_) (fun _ _ _ => by positivity)
        exact Fintype.mem_piFinset.2 fun k => Finset.mem_image_of_mem _ hν
    _ = ∏ k, ∑ j ∈ (s.image (fun ν => ν k) : Finset ℤ), 1 / (1 + |(j : ℝ)|) ^ 2 := by
        exact (Finset.prod_univ_sum (fun k => (s.image (fun ν => ν k) : Finset ℤ))
          (fun _ j => 1 / (1 + |(j : ℝ)|) ^ 2)).symm
    _ ≤ _ := by
        refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
        exact summable_int_weight.sum_le_tsum _ (fun _ _ => by positivity)
end GlobalTheory.TorusElliptic
