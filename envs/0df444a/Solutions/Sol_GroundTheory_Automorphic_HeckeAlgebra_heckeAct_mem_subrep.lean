-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.heckeAct_mem_subrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:41.635071+00:00
-- url     : https://prove2.me/submissions/cc5fb817-7022-4e51-aa8a-6b38863c8572

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_heckeAct_mem_of_forall
import Theorems.Thm_GroundTheory_Automorphic_range_finite_of_mem_locallyConstantCompactSupport


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
theorem _root_.solution (X : Subrepresentation ρ) {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {x : V} (hx : x ∈ smoothVectors ρ)
    (hX : x ∈ X) : heckeAct μ ρ f x ∈ X :=
  heckeAct_mem_of_forall (X := X.toSubmodule)
    (range_finite_of_mem_locallyConstantCompactSupport (smul_orbit_mem hf hx))
    fun g => X.toSubmodule.smul_mem _ (X.apply_mem_toSubmodule g hX)
end GroundTheory.Automorphic.HeckeAlgebra
