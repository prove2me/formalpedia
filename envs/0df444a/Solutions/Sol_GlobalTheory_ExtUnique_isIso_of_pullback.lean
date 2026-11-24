-- Prove2me | solution 1 for GlobalTheory.ExtUnique.isIso_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:41:40.717779+00:00
-- url     : https://prove2.me/submissions/b51218f8-8416-4cff-add5-2d10f3160be1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_comp_eq_id_of_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{u}} (j : U ⟶ S) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
namespace GlobalTheory.ExtUnique
theorem _root_.solution {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    (e : (Over.pullback j).obj X ≅ (Over.pullback j).obj Y) (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : (Over.pullback j).map f = e.hom) (hg : (Over.pullback j).map g = e.inv) : IsIso f :=
  ⟨g, comp_eq_id_of_pullback j e f g hf hg⟩
end GlobalTheory.ExtUnique
