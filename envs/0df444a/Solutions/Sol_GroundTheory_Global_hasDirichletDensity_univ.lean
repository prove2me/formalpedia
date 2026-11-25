-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:32.114739+00:00
-- url     : https://prove2.me/submissions/14716aae-93ae-481c-bcf5-abd4a82528fb

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
theorem _root_.solution : (univ : Set (HeightOneSpectrum (𝓞 K))).HasDirichletDensity 1 := by
  unfold Set.HasDirichletDensity
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm
end GroundTheory.Global
