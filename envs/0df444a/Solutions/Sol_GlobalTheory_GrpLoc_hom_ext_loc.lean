-- Prove2me | solution 1 for GlobalTheory.GrpLoc.hom_ext_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:51.055857+00:00
-- url     : https://prove2.me/submissions/aa646b52-0667-40b6-8d51-3931360bc6d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsGrpPullbackLocalOnBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.GrpLoc
namespace GlobalTheory.GrpLoc
theorem _root_.solution {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp hfg using h
  exact Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) X W a
    (fun x => by obtain ⟨y, hy⟩ := hp x; exact ⟨x, y, hy⟩) ha) f g hfg
end GlobalTheory.GrpLoc
