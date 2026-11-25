-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.distChar_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:58:24.001351+00:00
-- url     : https://prove2.me/submissions/c4ef87d5-b420-45ee-973c-0da65dac98b4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_heckeAct_comp

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
theorem _root_.solution (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hμ : μ.map α = μ) (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ (ρ.comp α.toMonoidHom) (isAdmissible_comp α hα hα' hρ) f =
      distChar μ ρ hρ (compHomeoL (mulEquivHomeo α hα hα').symm f) := by
  rw [distChar_apply, distChar_apply]
  congr 1
  exact LinearMap.ext fun v =>
    heckeAct_comp μ α hα hα' hμ f (hρ.1 v) ((isAdmissible_comp α hα hα' hρ).1 v)
end GroundTheory.Automorphic.ContragredientTranspose
