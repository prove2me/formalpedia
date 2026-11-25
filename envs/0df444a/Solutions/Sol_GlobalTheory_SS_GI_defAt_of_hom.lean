-- Prove2me | solution 1 for GlobalTheory.SS.GI.defAt_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:24.052955+00:00
-- url     : https://prove2.me/submissions/86274ff4-e6d6-4062-844e-239cb7fa0d04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_defAt_iff

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
theorem _root_.solution {M : Model R A} {N : Model R A'} {f : A ⟶ A'} (g : M.Y ⟶ N.Y)
    (h : M.j ≫ g.left = f.left ≫ N.j) (y : M.Y.left) : DefAt M N f y :=
  defAt_iff.2 ⟨_, _, _, y, inferInstance, rfl, via_of_hom g h⟩
end GlobalTheory.SS.GI
