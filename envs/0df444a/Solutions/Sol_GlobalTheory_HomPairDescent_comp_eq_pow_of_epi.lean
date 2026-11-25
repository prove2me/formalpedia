-- Prove2me | solution 1 for GlobalTheory.HomPairDescent.comp_eq_pow_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:28:06.621793+00:00
-- url     : https://prove2.me/submissions/69c61d3c-b2fc-4017-968a-3431329890cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomPairDescendsToFinite
import Theorems.Thm_GlobalTheory_HomPairDescent_id_pow_left_comm

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
theorem _root_.solution {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] {G' H' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G j φ) [Epi φ]
    {a' : G' ⟶ H'} {b' : H' ⟶ G'} {a : G ⟶ H} {b : H ⟶ G}
    (ha : φ ≫ a.left = a'.left ≫ ψ) (hb : ψ ≫ b.left = b'.left ≫ φ) (m : ℕ)
    (e : a' ≫ b' = 𝟙 _ ^ m) : a ≫ b = 𝟙 _ ^ m := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi φ, ← id_pow_left_comm h m, ← e, Over.comp_left, Over.comp_left, reassoc_of% ha, hb,
    Category.assoc]
end GlobalTheory.HomPairDescent
