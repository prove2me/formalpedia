-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.heckeAct_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:10:05.842505+00:00
-- url     : https://prove2.me/submissions/88188fa4-a23a-4ddf-901c-2bd4e5a0aa5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_mul

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
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution {v : V} (hv : v ∈ fixedVectors ρ K) (f : HeckeAlgebra μ) :
    heckeAct μ ρ (HeckeAlgebraLevel.corner hKc hKo f : HeckeAlgebra μ) v =
      heckeAct μ ρ (idem μ hKc hKo * f : HeckeAlgebra μ) v := by
  rw [HeckeAlgebraLevel.val_corner, heckeAct_mul _ _ (smooth_of_mem_fixedVectors hKo hv),
    heckeAct_idem_of_mem (μ := μ) hKc hKo hv]
end GroundTheory.Automorphic.HeckeAlgebra
