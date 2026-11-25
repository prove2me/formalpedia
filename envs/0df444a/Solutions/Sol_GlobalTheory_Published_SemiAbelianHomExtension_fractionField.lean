-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:32:52.041415+00:00
-- url     : https://prove2.me/submissions/f0b57e4d-7af9-40db-850b-91bd32a27044

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_IsGenericPointHom_fractionField
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isGenericPointHom
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isNormalScheme_spec

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
universe u
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : GlobalTheory.Published.SemiAbelianHomExtension) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f :=
  of_isGenericPointHom h (isNormalScheme_spec R) (GlobalTheory.IsGenericPointHom.fractionField R K) hG hH f
end GlobalTheory.Published.SemiAbelianHomExtension
