-- Prove2me | solution 1 for GlobalTheory.HomPairDescent.id_pow_left_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:07.944665+00:00
-- url     : https://prove2.me/submissions/b3d86ecb-1d30-4ad9-8883-1b692a985182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomPairDescendsToFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.HomPairDescent
open GlobalTheory.Spread
namespace GlobalTheory.HomPairDescent
theorem _root_.solution {S S' : Scheme.{0}} {j : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G j φ) (m : ℕ) :
    (𝟙 G' ^ m : G' ⟶ G').left ≫ φ = φ ≫ (𝟙 G ^ m : G ⟶ G).left := by
  have e₁ := congrArg (fun a => a.left) (map_pow (pushHom h G') (𝟙 G') m)
  have e₂ := congrArg (fun a => a.left) (MonObj.comp_pow (𝟙 G) m (pushHom h G' (𝟙 G')))
  rw [Category.comp_id] at e₂
  refine e₁.trans (e₂.symm.trans ?_)
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]
end GlobalTheory.HomPairDescent
