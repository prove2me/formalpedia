-- Prove2me | solution 1 for GlobalTheory.SS.GI.isoAt_braiding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:41.52122+00:00
-- url     : https://prove2.me/submissions/0b530ef7-3f77-4877-8c82-84de9c09fa72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_isoAt_iff

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
namespace GlobalTheory.SS.GI
theorem _root_.solution (M : Model R A) (N : Model R A') (z : (M.prod N).Y.left) :
    IsoAt (M.prod N) (N.prod M) (β_ A A').hom z := by
  have : IsIso (β_ M.Y N.Y).hom.left := inferInstanceAs (IsIso ((Over.forget (Sp R)).map (β_ M.Y N.Y).hom))
  refine isoAt_iff.2 ⟨_, 𝟙 _, (β_ M.Y N.Y).hom.left, z, inferInstance, inferInstance, rfl, ?_⟩
  refine via_prod ?_ ?_
  · have e : (β_ M.Y N.Y).hom.left ≫ (fst N.Y M.Y).left = 𝟙 _ ≫ (snd M.Y N.Y).left :=
      congr(($(braiding_hom_fst M.Y N.Y)).left)
    rw [braiding_hom_fst, e]
    exact via_snd M N _
  · have e : (β_ M.Y N.Y).hom.left ≫ (snd N.Y M.Y).left = 𝟙 _ ≫ (fst M.Y N.Y).left :=
      congr(($(braiding_hom_snd M.Y N.Y)).left)
    rw [braiding_hom_snd, e]
    exact via_fst M N _
end GlobalTheory.SS.GI
