-- Prove2me | solution 1 for GlobalTheory.IsGenericPointHom.quasiCompact_and_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:37.242843+00:00
-- url     : https://prove2.me/submissions/1c548290-2088-41f0-87a8-f44a3359421c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_IsGenericPointHom_quasiCompact_and_dominant_of_comp

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
open GlobalTheory
open ExtUnique
open GlobalTheory.IsGenericPointHom
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}
namespace GlobalTheory.IsGenericPointHom
theorem _root_.solution [IsLocallyNoetherian S] (hj : IsGenericPointHom j) :
    QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  quasiCompact_and_dominant_of_comp (i := 𝟙 S) (by rwa [Category.comp_id])
end GlobalTheory.IsGenericPointHom
