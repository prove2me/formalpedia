-- Prove2me | solution 1 for GlobalTheory.RationalPoint.separatelyContinuousMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:53.961345+00:00
-- url     : https://prove2.me/submissions/89641b0c-89ef-46e3-8182-234e2d4f1aaa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Theorems.Thm_GlobalTheory_RationalPoint_continuous_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
open GlobalTheory
open GlobalTheory.RationalPoint
variable {k : Type} [Field k]
namespace GlobalTheory.RationalPoint
theorem _root_.solution (B : Over (Sp k)) [GrpObj B] :
    @SeparatelyContinuousMul (𝟙_ (Over (Sp k)) ⟶ B) (zariski B) _ := by
  letI := zariski B
  have h : ∀ g y : 𝟙_ (Over (Sp k)) ⟶ B, y ≫ toUnit B ≫ g = g := fun g y => by
    rw [← Category.assoc, toUnit_unique (y ≫ toUnit B) (𝟙 _), Category.id_comp]
  refine ⟨fun {g} => ?_, fun {g} => ?_⟩
  · convert continuous_comp ((toUnit B ≫ g) * 𝟙 B) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]
  · convert continuous_comp (𝟙 B * (toUnit B ≫ g)) using 2 with y
    rw [MonObj.comp_mul, h, Category.comp_id]
end GlobalTheory.RationalPoint
