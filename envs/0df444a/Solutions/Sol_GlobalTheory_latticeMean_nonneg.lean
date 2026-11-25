-- Prove2me | solution 1 for GlobalTheory.latticeMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:24.230173+00:00
-- url     : https://prove2.me/submissions/0324e29c-7d4e-40f0-b70a-5ac3958c5e19

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
theorem _root_.solution {f : E → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ latticeMean L f := by
  borelize E
  simp only [latticeMean_eq_integral]
  exact integral_nonneg hf
end GlobalTheory
