-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:33.914913+00:00
-- url     : https://prove2.me/submissions/5d8e01ff-0d9d-469e-b719-ef9684c5137e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isOpenImmersion
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isOpenImmersion_generic_dvr
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isDominant_generic_dvr
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isNormalScheme_dvr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
variable (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]
variable {T K}
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : SemiAbelianHomExtension) {G H : Over (Sp T)} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj H)
    [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f :=
  have := isOpenImmersion_generic_dvr T K
  have := isDominant_generic_dvr T K
  h.of_isOpenImmersion (isNormalScheme_dvr T) _ hG hH f
end GlobalTheory.Published.SemiAbelianHomExtension
