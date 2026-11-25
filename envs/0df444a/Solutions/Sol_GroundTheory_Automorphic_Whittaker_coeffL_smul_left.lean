-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:14:05.609856+00:00
-- url     : https://prove2.me/submissions/da1c545b-82f8-4d21-873d-eb3b255e1abb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
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
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (c : ℂ) (ℓ : Module.Dual ℂ V) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ (c • ℓ) f = c • coeffL μ hρ ℓ f :=
  Subtype.ext (LinearMap.ext fun v => by
    simp only [coeffL_apply, SetLike.val_smul, LinearMap.smul_apply])
end GroundTheory.Automorphic.Whittaker
