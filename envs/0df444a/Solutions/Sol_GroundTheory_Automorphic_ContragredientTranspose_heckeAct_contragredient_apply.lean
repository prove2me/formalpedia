-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.heckeAct_contragredient_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:38.74086+00:00
-- url     : https://prove2.me/submissions/579bfb9d-051f-428e-a476-27cd0ac55e45

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient


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
theorem _root_.solution [μ.IsInvInvariant] (hρ : IsSmooth ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) (ξ : smoothVectors (Representation.dual ρ)) (v : V) :
    ((heckeAct μ (contragredient ρ) (f : G → ℂ) ξ : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) v =
      (ξ : Module.Dual ℂ V) (heckeAct μ ρ
        ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v) := by
  have h1 := dual_heckeAct μ f.2 (isSmooth_contragredient ρ ξ) (evalSmooth ρ v)
  have key := integral_inv_eq_self (fun g =>
    ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) g *
      (ξ : Module.Dual ℂ V) (ρ g v)) μ
  beta_reduce at key
  rw [evalSmooth_apply] at h1
  rw [h1, dual_heckeAct μ (compHomeoL (Homeomorph.inv G) f).2 (hρ v), ← key]
  congr 1
  funext g
  simp [evalSmooth_apply, contragredient_apply_apply]
end GroundTheory.Automorphic.ContragredientTranspose
