-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.isSmooth_quotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:48:59.907809+00:00
-- url     : https://prove2.me/submissions/3ab3ea05-06eb-4c04-b21c-23684d979884

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
open HeckeAlgebraLevel
variable (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution : IsSmooth (quotRep hKc hKo I) := by
  intro y
  obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective y
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (leftReg μ) φ) (fun g hg => ?_)
    (isSmooth_leftReg φ)
  rw [mem_stabilizerOf, quotRep_mkQ, mem_stabilizerOf.1 hg]
end GroundTheory.Automorphic.HeckeAlgebra
