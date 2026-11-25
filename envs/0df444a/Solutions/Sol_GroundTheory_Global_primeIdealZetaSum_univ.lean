-- Prove2me | solution 1 for GroundTheory.Global.primeIdealZetaSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:52.046824+00:00
-- url     : https://prove2.me/submissions/a1b7810a-d400-4d6f-8a75-bb9705131ffb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole

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
theorem _root_.solution (s : ℝ) :
    (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-s) := by
  rw [Set.primeIdealZetaSum_def]
  exact tsum_univ (f := fun w : HeightOneSpectrum (𝓞 K) => (absNorm w.asIdeal : ℝ) ^ (-s))
end GroundTheory.Global
