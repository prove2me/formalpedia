-- Prove2me | solution 1 for GlobalTheory.TorusLocal.eq_one_of_isNilpotent_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:43:37.741826+00:00
-- url     : https://prove2.me/submissions/5b89fa69-640b-4ed4-b330-8dc75d2d123f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Theorems.Thm_GlobalTheory_TorusLocal_pullback_map_eq_one
import Theorems.Thm_GlobalTheory_splitTorus_hom_eq_one_of_nilpotent
import Theorems.Thm_GlobalTheory_splitTorus_hom_proper_trivial_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusLocal
namespace GlobalTheory.TorusLocal
theorem _root_.solution (A : Type) [CommRing A] [IsLocalRing A]
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of A))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  refine splitTorus_hom_eq_one_of_nilpotent A _ hA X B f hf (pullback_map_eq_one _ X B f hf ?_)
  intro g hg
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_field (A ⧸ IsLocalRing.maximalIdeal A) X _ g hg
end GlobalTheory.TorusLocal
