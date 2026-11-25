-- Prove2me | solution 1 for GlobalTheory.HolFibre.isHolTo_fibPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:09:53.747681+00:00
-- url     : https://prove2.me/submissions/82c50efc-d765-4426-9ef8-8957ba7c1ca5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_const
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolFibre
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.HolFibre
theorem _root_.solution {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (G : Over X) (y : Sp ℂ ⟶ X)
    (e : E → (Over.mk y ⟶ G)) (he : IsHolTo W (fun z => (e z).left)) :
    IsHolTo W (fun z => fibPt G (e z)) := by
  refine isHolTo_of_isPullback (IsPullback.of_hasPullback G.hom y) ?_ ?_
  · simp only [fibPt, pullback.lift_fst]
    exact he
  · simp only [fibPt, pullback.lift_snd]
    exact isHolTo_const hW _
end GlobalTheory.HolFibre
