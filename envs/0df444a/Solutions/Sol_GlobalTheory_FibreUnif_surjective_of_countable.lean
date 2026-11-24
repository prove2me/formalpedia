-- Prove2me | solution 1 for GlobalTheory.FibreUnif.surjective_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:41:47.599798+00:00
-- url     : https://prove2.me/submissions/8eaa999e-0ae9-4ade-a6cd-64c16dd6775c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_FamilyUniformisationFibreTheta
import Theorems.Thm_GlobalTheory_FibreUnif_eq_zero_of_smul_mem_countable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.FibreUnif
namespace GlobalTheory.FibreUnif
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (F : V →ₗ[ℂ] W) {C : Set W} (hC : C.Countable) (h : ∀ w, ∃ z, w - F z ∈ C) : Function.Surjective F := by
  intro w
  have : (LinearMap.range F).mkQ w = 0 := by
    refine eq_zero_of_smul_mem_countable (hC.image (LinearMap.range F).mkQ) fun t => ?_
    obtain ⟨z, hz⟩ := h (t • w)
    refine ⟨_, hz, ?_⟩
    have : (LinearMap.range F).mkQ (F z) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
    rw [map_sub, this, sub_zero, map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).1 this
end GlobalTheory.FibreUnif
