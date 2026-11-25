-- Prove2me | solution 1 for GroundTheory.Global.dedekindZetaReal_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:03.612364+00:00
-- url     : https://prove2.me/submissions/db1b1c88-0c8f-45a3-b5dc-06e6ad1c45d4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_dedekindZetaTerm_nonneg
import Theorems.Thm_GroundTheory_Global_sum_range_dedekindZetaTerm
import Theorems.Thm_GroundTheory_Global_sum_rpow_neg_le_exp_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hs : 1 < s) :
    dedekindZetaReal K s ≤
      Real.exp (∑' w : HeightOneSpectrum (𝓞 K),
        ((absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)) := by
  refine Real.tsum_le_of_sum_range_le (fun n => dedekindZetaTerm_nonneg K s n) fun N => ?_
  rw [sum_range_dedekindZetaTerm]
  exact sum_rpow_neg_le_exp_tsum _ hs
end GroundTheory.Global
