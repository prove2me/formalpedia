-- Prove2me | solution 1 for GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:35.53232+00:00
-- url     : https://prove2.me/submissions/c8918103-7530-49fd-bdd5-1cd892f516d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant

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
variable {j}
namespace GlobalTheory.ExtUnique
theorem _root_.solution {X Y : Over S} [Flat X.hom] [IsSeparated Y.hom] {X' : Scheme.{u}}
    {φ : X' ⟶ X.left} {p : X' ⟶ U} (h : IsPullback φ p X.hom j) {f g : X ⟶ Y}
    (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback h.flip
  exact Over.OverMorphism.ext (hom_ext_of_dominant Y.hom (by rw [Over.w, Over.w]) φ hfg)
end GlobalTheory.ExtUnique
