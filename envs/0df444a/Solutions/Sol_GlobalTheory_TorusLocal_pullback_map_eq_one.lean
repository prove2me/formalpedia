-- Prove2me | solution 1 for GlobalTheory.TorusLocal.pullback_map_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:24:49.830193+00:00
-- url     : https://prove2.me/submissions/514f38e5-93da-41c2-8591-2bd09b85a938

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Theorems.Thm_GlobalTheory_splitTorus_baseChange


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
theorem _root_.solution {S S' : Scheme.{0}} (p : S' ⟶ S) (X : Type) [AddCommGroup X]
    (B : Over S) [GrpObj B] (f : splitTorus S X ⟶ B) (hf : IsMonHom f)
    (h : ∀ g : splitTorus S' X ⟶ (Over.pullback p).obj B, IsMonHom g →
      g = toUnit _ ≫ η[(Over.pullback p).obj B]) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨e, he, -⟩ := splitTorus_baseChange S S' p X
  have h1 : e.hom ≫ (Over.pullback p).map f = 1 := h _ inferInstance
  have h2 : (Over.pullback p).map (1 : splitTorus S X ⟶ B) = 1 := Functor.map_one _
  rw [← cancel_epi e.hom, h1, ← Hom.one_def, h2, MonObj.comp_one]
end GlobalTheory.TorusLocal
