-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.distChar_biTranslL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:58:50.345147+00:00
-- url     : https://prove2.me/submissions/3687b550-95f0-4e92-a751-3ef465d665c5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_finTrace_conj
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_heckeAct_biTranslL

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution [μ.IsMulRightInvariant] (hρ : IsAdmissible ρ) (g : G)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ ρ hρ (biTranslL g g f) = distChar μ ρ hρ f := by
  have := finiteDimensional_range_heckeLin μ hρ f
  have e : heckeLin μ hρ.1 (biTranslL g g f) = (repEquiv ρ g).conj (heckeLin μ hρ.1 f) :=
    LinearMap.ext fun v => by
      rw [LinearEquiv.conj_apply, heckeLin_apply, heckeAct_biTranslL μ hρ.1 g f v]
      rfl
  rw [distChar_apply, distChar_apply, e, finTrace_conj]
end GroundTheory.Automorphic.ContragredientTranspose
