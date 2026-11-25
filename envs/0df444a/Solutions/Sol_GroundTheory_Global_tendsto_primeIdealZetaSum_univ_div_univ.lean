-- Prove2me | solution 1 for GroundTheory.Global.tendsto_primeIdealZetaSum_univ_div_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:38.720801+00:00
-- url     : https://prove2.me/submissions/1b2d9efd-81d2-4fbb-98ce-675d6dad1373

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_tendsto_neg_log_sub_one_atTop
import Theorems.Thm_GroundTheory_Global_tendsto_primeIdealZetaSum_univ_div_neg_log

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
namespace GroundTheory.Global
theorem _root_.solution (L : Type*) [Field L] [NumberField L] :
    Tendsto (fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s /
      (univ : Set (HeightOneSpectrum (𝓞 L))).primeIdealZetaSum s) (𝓝[>] 1) (𝓝 1) := by
  have h := (tendsto_primeIdealZetaSum_univ_div_neg_log K).div
    (tendsto_primeIdealZetaSum_univ_div_neg_log L) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [tendsto_neg_log_sub_one_atTop.eventually_gt_atTop 0] with s hs
  exact div_div_div_cancel_right₀ hs.ne' _ _
end GroundTheory.Global
