-- Prove2me | solution 1 for GlobalTheory.SS.FrobField.isMonHom_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:16:34.65234+00:00
-- url     : https://prove2.me/submissions/e176470a-f858-4fd2-a563-0e04f0f19024

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobField
namespace GlobalTheory.SS.FrobField
theorem _root_.solution {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (P : C ⥤ D) [P.Monoidal] (α : P ⟶ P) (G : C) [MonObj G] :
    IsMonHom (α.app G) where
  one_hom := by
    rw [Functor.obj.η_def, Category.assoc, α.naturality, ← Category.assoc, NatTrans.IsMonoidal.unit]
  mul_hom := by
    rw [Functor.obj.μ_def, Category.assoc, α.naturality, ← Category.assoc, NatTrans.IsMonoidal.tensor,
      Category.assoc]
end GlobalTheory.SS.FrobField
