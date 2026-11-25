-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_zero_of_isBoundedUnder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:56:27.744989+00:00
-- url     : https://prove2.me/submissions/74756c8f-9aa6-4091-ad9f-64586f6a37c2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_tendsto_primeIdealZetaSum_univ_atTop


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
theorem _root_.solution {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => S.primeIdealZetaSum s) :
    S.HasDirichletDensity 0 := by
  obtain ⟨C, hC⟩ := hS
  have hC' : ∀ᶠ s in 𝓝[>] (1 : ℝ), S.primeIdealZetaSum s ≤ C := eventually_map.mp hC
  have hden := tendsto_primeIdealZetaSum_univ_atTop K
  have hpos := hden.eventually_gt_atTop 0
  unfold Set.HasDirichletDensity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Tendsto.div_atTop (tendsto_const_nhds (x := C)) hden) (Eventually.of_forall fun s => ?_) ?_
  · exact div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)
  · filter_upwards [hC', hpos] with s h1 h2
    exact div_le_div_of_nonneg_right h1 h2.le
end GroundTheory.Global
