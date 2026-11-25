-- Prove2me | solution 1 for GlobalTheory.HomPairDescent.isGrpPullback_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:40.788428+00:00
-- url     : https://prove2.me/submissions/018e8d5b-06ce-486d-8f8f-489dd55e4842

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomPairDescendsToFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_cancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
theorem _root_.solution {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)
end GlobalTheory.HomPairDescent
