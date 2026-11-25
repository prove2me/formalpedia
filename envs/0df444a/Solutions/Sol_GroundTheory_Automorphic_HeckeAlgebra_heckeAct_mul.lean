-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.heckeAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:45.814044+00:00
-- url     : https://prove2.me/submissions/f7d83a68-bc3e-4f56-8a37-4169a8b744ca

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [μ.IsHaarMeasure]
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (a b : HeckeAlgebra μ)
    {v : V} (hv : v ∈ smoothVectors ρ) :
    heckeAct μ ρ (a * b : HeckeAlgebra μ) v = heckeAct μ ρ a (heckeAct μ ρ b v) := by
  rw [coe_mul]
  exact heckeAct_groupConv a.mem b.mem hv
end GroundTheory.Automorphic.HeckeAlgebra
