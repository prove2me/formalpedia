-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_equivariantFunctionals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:22.698246+00:00
-- url     : https://prove2.me/submissions/ea292f22-ef6e-4a54-a4aa-b2744a229d08

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {ρ : Representation ℂ G V} {H : Subgroup G} {χ : H → ℂ}
    {ℓ : Module.Dual ℂ V} :
    ℓ ∈ equivariantFunctionals ρ χ ↔ ∀ h : H, ∀ v, ℓ (ρ h v) = χ h * ℓ v :=
  Iff.rfl
end GroundTheory.Automorphic.Whittaker
