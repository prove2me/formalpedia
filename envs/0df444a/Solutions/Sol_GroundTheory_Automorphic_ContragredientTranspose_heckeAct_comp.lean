-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.heckeAct_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:54.754466+00:00
-- url     : https://prove2.me/submissions/75a6cfec-bc7a-4705-8fe1-55079e98577e

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (α : G ≃* G) (hα : Continuous α) (hα' : Continuous α.symm)
    (hμ : μ.map α = μ) (f : locallyConstantCompactSupport G ℂ ℂ) {v : V}
    (hv : v ∈ smoothVectors ρ) (hv' : v ∈ smoothVectors (ρ.comp α.toMonoidHom)) :
    heckeAct μ (ρ.comp α.toMonoidHom) (f : G → ℂ) v =
      heckeAct μ ρ ((compHomeoL (mulEquivHomeo α hα hα').symm f :
        locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ f.2 hv', dual_heckeAct μ (compHomeoL _ f).2 hv]
  have hmp : MeasurePreserving (mulEquivHomeo α hα hα').toMeasurableEquiv μ μ :=
    ⟨hα.measurable, hμ⟩
  have key := hmp.integral_comp' (fun g =>
    ((compHomeoL (mulEquivHomeo α hα hα').symm f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) g *
      φ (ρ g v))
  beta_reduce at key
  rw [← key]
  congr 1
  funext g
  simp
end GroundTheory.Automorphic.ContragredientTranspose
