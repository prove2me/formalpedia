-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isMonHom_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:32.287218+00:00
-- url     : https://prove2.me/submissions/49884924-e247-4621-af32-9b01ce5fbaf4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Theorems.Thm_GlobalTheory_FieldBaseChange_pullback_map_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.FieldBaseChange
variable {U S : Scheme.{0}} (j : U ⟶ S)
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution [Flat j] [Surjective j] {G H : Over S} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : IsMonHom ((Over.pullback j).map f)) : IsMonHom f := by
  constructor
  · apply pullback_map_injective j
    have h := hf.one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · apply pullback_map_injective j
    have h := hf.mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]
end GlobalTheory.FieldBaseChange
