-- Prove2me | solution 1 for GlobalTheory.SS.GI.isoAt_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:16:40.627088+00:00
-- url     : https://prove2.me/submissions/b2edfb7a-79df-4bde-915a-fc7279807da7

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
theorem _root_.solution (M : Model R A) (N : Model R A') (P : Model R A'') (z : ((M.prod N).prod P).Y.left) :
    IsoAt ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom z := by
  have : IsIso (α_ M.Y N.Y P.Y).hom.left := inferInstanceAs (IsIso ((Over.forget (Sp R)).map (α_ M.Y N.Y P.Y).hom))
  refine isoAt_iff.2 ⟨_, 𝟙 _, (α_ M.Y N.Y P.Y).hom.left, z, inferInstance, inferInstance, rfl, ?_⟩
  have h := via_fst (M.prod N) P (𝟙 _)
  refine via_prod ?_ (via_prod ?_ ?_)
  · have e : (α_ M.Y N.Y P.Y).hom.left ≫ (fst M.Y (N.prod P).Y).left =
        (𝟙 _ ≫ (fst (M.prod N).Y P.Y).left) ≫ (fst M.Y N.Y).left :=
      congr(($(associator_hom_fst M.Y N.Y P.Y)).left)
    rw [associator_hom_fst, e]
    exact h.comp (via_fst M N _)
  · have e : ((α_ M.Y N.Y P.Y).hom.left ≫ (snd M.Y (N.prod P).Y).left) ≫ (fst N.Y P.Y).left =
        (𝟙 _ ≫ (fst (M.prod N).Y P.Y).left) ≫ (snd M.Y N.Y).left := by
      rw [Category.assoc]
      exact congr(($(associator_hom_snd_fst M.Y N.Y P.Y)).left)
    rw [Category.assoc, associator_hom_snd_fst, e]
    exact h.comp (via_snd M N _)
  · have e : ((α_ M.Y N.Y P.Y).hom.left ≫ (snd M.Y (N.prod P).Y).left) ≫ (snd N.Y P.Y).left =
        (𝟙 _ ≫ (snd (M.prod N).Y P.Y).left) := by
      rw [Category.assoc]
      exact congr(($(associator_hom_snd_snd M.Y N.Y P.Y)).left)
    rw [Category.assoc, associator_hom_snd_snd, e]
    exact via_snd (M.prod N) P _
end GlobalTheory.SS.GI
