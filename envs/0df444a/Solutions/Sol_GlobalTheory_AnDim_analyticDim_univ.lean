-- Prove2me | solution 1 for GlobalTheory.AnDim.analyticDim_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:09.535871+00:00
-- url     : https://prove2.me/submissions/10c329b4-7530-4c69-b598-9ee57bae34e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_le_analyticDim
import Theorems.Thm_GlobalTheory_AnDim_analyticDim_le
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_BoundaryPolynomialFunctions_regularLocus_univ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution [Nonempty X] (A : FinHolAtlas d X) : analyticDim A Set.univ = d :=
  le_antisymm (analyticDim_le A _)
    (le_analyticDim (by rw [regularLocus_univ]; exact Set.univ_nonempty))
end GlobalTheory.AnDim
