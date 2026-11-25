-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.heckeAct_biTranslL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:51.140016+00:00
-- url     : https://prove2.me/submissions/a5355e95-3f0f-49b4-b4ce-250a864404bb

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
theorem _root_.solution [μ.IsMulRightInvariant] (hρ : IsSmooth ρ) (g : G)
    (f : locallyConstantCompactSupport G ℂ ℂ) (v : V) :
    heckeAct μ ρ ((biTranslL g g f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) v =
      ρ g (heckeAct μ ρ f (ρ g⁻¹ v)) := by
  have hf' : (fun x => (f : G → ℂ) (x * g⁻¹⁻¹)) ∈ locallyConstantCompactSupport G ℂ ℂ := by
    simpa using (rtransL g f).2
  rw [heckeAct_apply_act μ f.2 (hρ v) g⁻¹, heckeAct_ltrans g hf' (hρ v)]
  congr 1
  funext x
  simp [ltrans_apply, mul_assoc]
end GroundTheory.Automorphic.ContragredientTranspose
