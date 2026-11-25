-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.distChar_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:54.402886+00:00
-- url     : https://prove2.me/submissions/5f332031-d92a-477b-92f1-f056892451d2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_apply

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
theorem _root_.solution (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ)
    {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hK : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    distChar μ ρ hρ f = LinearMap.trace ℂ (fixedVectors ρ K) ((heckeLin μ hρ.1 f).restrict
      fun x _ => range_heckeLin_le μ hρ.1 f hK (LinearMap.mem_range_self _ x)) := by
  have := hρ.2 K hKc hKo
  rw [distChar_apply, finTrace_eq_trace _ _ (range_heckeLin_le μ hρ.1 f hK)]
end GroundTheory.Automorphic.ContragredientTranspose
