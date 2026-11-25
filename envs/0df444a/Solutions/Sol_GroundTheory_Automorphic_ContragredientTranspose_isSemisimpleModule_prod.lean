-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.isSemisimpleModule_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:40.115196+00:00
-- url     : https://prove2.me/submissions/545b9048-9767-4b96-a62e-ad0f284e1f6c

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
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  have h1 : IsSemisimpleModule R (LinearMap.range (LinearMap.inl R M N)) :=
    IsSemisimpleModule.range _
  have h2 : IsSemisimpleModule R (LinearMap.range (LinearMap.inr R M N)) :=
    IsSemisimpleModule.range _
  have h := IsSemisimpleModule.sup h1 h2
  rw [LinearMap.sup_range_inl_inr] at h
  exact IsSemisimpleModule.congr (Submodule.topEquiv (R := R) (M := M × N)).symm
end GroundTheory.Automorphic.ContragredientTranspose
