-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_normInd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:19:53.396781+00:00
-- url     : https://prove2.me/submissions/ad35c213-25ad-4563-aad5-d2f22167a17d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_heckeAct_normInd
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_apply

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
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable (hρ : IsSmooth ρ)
include hρ
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {v : V} (hv : v ∈ fixedVectors ρ K) :
    ((coeffL μ hρ ℓ ⟨normInd μ K, normInd_mem μ hKc hKo⟩ : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) v = ℓ v := by
  rw [coeffL_apply]
  exact congrArg ℓ (heckeAct_normInd μ hKc hKo hv)
end GroundTheory.Automorphic.Whittaker
