-- Prove2me | solution 1 for GlobalTheory.isMonHom_of_comp_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:13.762081+00:00
-- url     : https://prove2.me/submissions/202a10a6-3f6c-4e7c-9c74-62f127946c2b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed

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
open GlobalTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
namespace GlobalTheory
theorem _root_.solution {A B D : C} [MonObj A] [MonObj B] [MonObj D] (e : A ⟶ B) (i : B ⟶ D)
    [Mono i] [IsMonHom i] [h : IsMonHom (e ≫ i)] : IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, h.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]
end GlobalTheory
