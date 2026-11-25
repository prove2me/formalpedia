-- Prove2me | solution 1 for GroundTheory.Automorphic.map_heckeAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:55.410801+00:00
-- url     : https://prove2.me/submissions/97f113be-d894-4371-b7dc-69e2b672289b

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
variable (μ : Measure G) {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {μ} {ρ : Representation ℂ G V}
variable [IsFiniteMeasureOnCompacts μ]
namespace GroundTheory.Automorphic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (T : Representation.IntertwiningMap ρ σ) {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {v : V} (hv : v ∈ smoothVectors ρ) :
    T (heckeAct μ ρ f v) = heckeAct μ σ f (T v) := by
  have hTv : T v ∈ smoothVectors σ := Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v)
    (fun g hg => by rw [mem_stabilizerOf, ← T.isIntertwining, mem_stabilizerOf.1 hg]) hv
  refine eq_of_forall_dual fun φ => ?_
  have := dual_heckeAct μ hf hv (φ ∘ₗ T.toLinearMap)
  simp only [LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply] at this
  rw [this, dual_heckeAct μ hf hTv]
  simp only [T.isIntertwining]
end GroundTheory.Automorphic
