-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.heckeRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:41.214776+00:00
-- url     : https://prove2.me/submissions/da902f91-77eb-4f6d-b30c-19eed5d01f08

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
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution (hρ : IsSmooth ρ) (f : HeckeAlgebra μ) (v : V) :
    heckeRep hρ f v = heckeAct μ ρ f v := rfl
end GroundTheory.Automorphic.HeckeAlgebra
