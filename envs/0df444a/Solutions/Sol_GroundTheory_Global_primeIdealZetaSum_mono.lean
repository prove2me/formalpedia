-- Prove2me | solution 1 for GroundTheory.Global.primeIdealZetaSum_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:25:06.593812+00:00
-- url     : https://prove2.me/submissions/015f0243-fe1f-4466-a433-cba38418f2ac

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg


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
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {A B : Set (HeightOneSpectrum (𝓞 K))} (hAB : A ⊆ B) {s : ℝ}
    (hs : 1 < s) : A.primeIdealZetaSum s ≤ B.primeIdealZetaSum s := by
  have h := summable_absNorm_rpow_neg (L := K) hs
  rw [Set.primeIdealZetaSum_def, Set.primeIdealZetaSum_def,
    tsum_subtype A (fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s)),
    tsum_subtype B (fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s))]
  exact Summable.tsum_le_tsum
    (fun w => indicator_le_indicator_of_subset hAB (fun _ => by positivity) w)
    (h.indicator A) (h.indicator B)
end GroundTheory.Global
