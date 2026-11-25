-- Prove2me | solution 1 for GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:41:50.20904+00:00
-- url     : https://prove2.me/submissions/1e8b95d9-ea0c-41db-bbf7-1ffe8b94cfa1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_exists_abs_primeIdealZetaSum_add_log_le

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
variable (K)
namespace GroundTheory.Global
theorem _root_.solution :
    Tendsto (fun s => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_add_log_le K
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨?_, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => show 0 < s - 1 by linarith⟩
    have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 0) := by
      simpa using (continuous_sub_right (1 : ℝ)).tendsto 1
    exact this.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun s : ℝ => -Real.log (s - 1) + -C) (𝓝[>] 1) atTop :=
    tendsto_atTop_add_const_right _ (-C)
      (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1))
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hC] with s hs
  have := (abs_le.mp hs).1
  linarith
end GroundTheory.Global
