-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.levelLin_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:41.421566+00:00
-- url     : https://prove2.me/submissions/fe0fba33-df5a-41d8-ac10-57e85e54fc1b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character

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
theorem _root_.solution (ρ : Representation ℂ G V) :
    levelLin hKc hKo ρ (1 : HeckeAlgebraLevel μ K hKc hKo) = LinearMap.id :=
  LinearMap.ext fun v => one_smul _ v
end GroundTheory.Automorphic.ContragredientTranspose
