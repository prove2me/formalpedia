-- Prove2me | solution 1 for GlobalTheory.latticeMean_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:23.463584+00:00
-- url     : https://prove2.me/submissions/6d490a90-f088-4b16-869a-2727a2007579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain

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
theorem _root_.solution {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (f : E → 𝕜) :
    latticeMean L (fun x => c * f x) = c * latticeMean L f := by
  borelize E
  simp only [latticeMean_eq_integral]
  exact integral_const_mul c f
end GlobalTheory
