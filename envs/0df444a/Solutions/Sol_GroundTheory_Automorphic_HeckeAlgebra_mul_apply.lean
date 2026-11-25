-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:47.674956+00:00
-- url     : https://prove2.me/submissions/907b534c-2b4e-4f51-8c80-5b1781d430c6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
open GroundTheory.Automorphic.HeckeAlgebra
variable {μ : Measure G}
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution (f g : HeckeAlgebra μ) (x : G) : (f * g) x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl
end GroundTheory.Automorphic.HeckeAlgebra
