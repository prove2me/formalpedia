-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:06:13.019981+00:00
-- url     : https://prove2.me/submissions/b9c77c2c-6cf6-4be5-b3d2-40017953be22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_of_isGenericPointHom

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
theorem _root_.solution (h : GlobalTheory.Published.SemiAbelianHomExtension) (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (S.fromSpecStalk (genericPoint S))).obj G ⟶ (Over.pullback (S.fromSpecStalk (genericPoint S))).obj H) [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (S.fromSpecStalk (genericPoint S))).map F = f :=
  of_isGenericPointHom h hS (GlobalTheory.IsGenericPointHom.fromSpecStalk S) hG hH f
end GlobalTheory.Published.SemiAbelianHomExtension
