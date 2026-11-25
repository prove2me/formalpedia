-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel.coe_smul_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:46.822988+00:00
-- url     : https://prove2.me/submissions/ee59a52b-4a32-4f8d-8f07-d6e95e76940e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel

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
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
open GroundTheory.Automorphic.HeckeAlgebra
variable (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (hKc : IsCompact (K : Set G))
  (hKo : IsOpen (K : Set G))
variable {μ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
open GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel
namespace GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel
theorem _root_.solution (h : HeckeAlgebraLevel μ K hKc hKo) (v : fixedVectors ρ K) :
    ((h • v : fixedVectors ρ K) : V) = heckeAct μ ρ (h : HeckeAlgebra μ) v := rfl
end GroundTheory.Automorphic.HeckeAlgebra.HeckeAlgebraLevel
