-- Prove2me | solution 1 for GlobalTheory.ExtUnique.pullback_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:52.818806+00:00
-- url     : https://prove2.me/submissions/d96ea4f2-82c3-4d78-afc7-2e549bd78810

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback
import Theorems.Thm_GlobalTheory_ExtUnique_pullback_map_left_fst

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
theorem _root_.solution (X Y : Over S) [Flat X.hom] [IsSeparated Y.hom] :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := fun f g h =>
  over_hom_ext_of_isPullback (IsPullback.of_hasPullback X.hom j)
    (by rw [← pullback_map_left_fst, ← pullback_map_left_fst, h])
end GlobalTheory.ExtUnique
