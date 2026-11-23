-- Prove2me | solution 1 for GlobalTheory.ExtUnique.comp_eq_id_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:53.819676+00:00
-- url     : https://prove2.me/submissions/331138e8-2c3b-4d61-81b5-496ea559b88a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback

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
theorem _root_.solution {X Y : Over S} [Flat X.hom] [IsSeparated X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    {X' Y' : Over U} {φ : X'.left ⟶ X.left} {ψ : Y'.left ⟶ Y.left}
    (hX : IsPullback φ X'.hom X.hom j) (hY : IsPullback ψ Y'.hom Y.hom j) (e : X' ≅ Y') (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : e.hom.left ≫ ψ = φ ≫ f.left) (hg : e.inv.left ≫ φ = ψ ≫ g.left) :
    f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · refine over_hom_ext_of_isPullback hX ?_
    rw [Over.comp_left, ← Category.assoc, ← hf, Category.assoc, ← hg, ← Category.assoc, ← Over.comp_left,
      e.hom_inv_id, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · refine over_hom_ext_of_isPullback hY ?_
    rw [Over.comp_left, ← Category.assoc, ← hg, Category.assoc, ← hf, ← Category.assoc, ← Over.comp_left,
      e.inv_hom_id, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
end GlobalTheory.ExtUnique
