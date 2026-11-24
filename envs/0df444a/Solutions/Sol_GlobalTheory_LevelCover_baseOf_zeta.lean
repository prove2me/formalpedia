-- Prove2me | solution 1 for GlobalTheory.LevelCover.baseOf_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:15.892672+00:00
-- url     : https://prove2.me/submissions/3d2afe4d-c2d5-4f2a-b024-17129b60b8bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
import Theorems.Thm_GlobalTheory_LevelCover_zeta_dvd

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
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.LevelCover
theorem _root_.solution (l l₂ : Level H) (F : IntermediateField ℚ ℂ) (h : KA l ≤ F) (h₂ : KA l₂ ≤ F) (hd : l.A ∣ l₂.A) :
    (baseOf l F h).ζ = (baseOf l₂ F h₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (IntermediateField.coe_inclusion h _).trans ((zeta_dvd l₂.A_pos hd).trans
    (congrArg (· ^ (l₂.A / l.A)) (IntermediateField.coe_inclusion h₂ (baseKA l₂).ζ).symm)))
end GlobalTheory.LevelCover
