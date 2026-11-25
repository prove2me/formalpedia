-- Prove2me | solution 1 for GlobalTheory.AnDim.le_analyticDim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:34.608788+00:00
-- url     : https://prove2.me/submissions/3d8e0e92-77b2-405a-aece-96db030ddb40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842

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
theorem _root_.solution {A : FinHolAtlas d X} {T : Set X} {n : ℕ}
    (h : (regularLocus A T n).Nonempty) : (n : WithBot ℕ∞) ≤ analyticDim A T :=
  le_iSup₂ (f := fun (n : ℕ) (_ : (regularLocus A T n).Nonempty) => (n : WithBot ℕ∞)) n h
end GlobalTheory.AnDim
