-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.distChar_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:26.273088+00:00
-- url     : https://prove2.me/submissions/615cfb49-7797-4ddc-83c2-7ed5659e6595

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_eq_trace

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
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
open HeckeAlgebra
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (h : HeckeAlgebraLevel μ K hKc hKo) :
    distChar μ ρ hρ (h : HeckeAlgebra μ) = LinearMap.trace ℂ (fixedVectors ρ K) (levelLin hKc hKo ρ h) := by
  rw [distChar_eq_trace μ hρ (h : HeckeAlgebra μ) hKc hKo
    (fun k hk x => HeckeAlgebraLevel.apply_mul_left hKc hKo h hk x)]
  rfl
end GroundTheory.Automorphic.ContragredientTranspose
