-- Prove2me | solution 1 for GlobalTheory.LevCover.act_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:07:21.493673+00:00
-- url     : https://prove2.me/submissions/1f99505c-52ef-4fab-84ca-5051128ee13d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitOnInjectiveOfCommRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Theorems.Thm_GlobalTheory_LevCover_add_map_nsmul


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
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) (c : 𝓞 E) :
    x ≫ t.act.act (n • c) = (x ^ n) ≫ t.act.act c := by
  have := t.act.hom c
  rw [add_map_nsmul t.act.add, MonObj.comp_pow, MonObj.pow_comp]
end GlobalTheory.LevCover
