-- Prove2me | solution 1 for GlobalTheory.latticeMean_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:19.088055+00:00
-- url     : https://prove2.me/submissions/aacb7d0d-8555-422a-8536-c08e0d12f784

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_integrable_latticeProb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → E → G}
    (hf : ∀ i ∈ s, Continuous (f i)) :
    latticeMean L (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, latticeMean L (f i) := by
  borelize E
  simp only [latticeMean_eq_integral]
  exact integral_finset_sum s fun i hi => integrable_latticeProb L (hf i hi)
end GlobalTheory
