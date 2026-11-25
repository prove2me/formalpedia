-- Prove2me | solution 1 for GlobalTheory.TwistLoc.fam_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:25.686606+00:00
-- url     : https://prove2.me/submissions/5dee28e8-6627-4225-8a93-178947850ed6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
namespace GlobalTheory.TwistLoc
theorem _root_.solution {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') (x : D'.X) (k : Fin 4) :
    D'.famφB x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) k := by
  have gp := pull_grp hD
  have he := hD.he
  have hc := hD.c_pr x
  generalize hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = F at gp he hc ⊢
  have pt : ∀ (y' : 𝟙_ _ ⟶ D'.P.A) (y : 𝟙_ _ ⟶ D.P.A), y'.left ≫ F = specOf φ ≫ y.left →
      (toUnit D'.P.A ≫ y').left ≫ F = F ≫ (toUnit D.P.A ≫ y).left := fun y' y e => by
    show (D'.P.A.hom ≫ y'.left) ≫ F = F ≫ D.P.A.hom ≫ y.left
    rw [Category.assoc, e, ← Category.assoc, ← gp.1.w, Category.assoc]
  fin_cases k
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · let U : Over.mk (D'.P.A.hom ≫ spMap φ) ⟶ D.P.A := Over.homMk F gp.1.w
    have m := gp.2 D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) (U ≫ 𝟙 _) (U ≫ toUnit _ ≫ D.c (hD.xe x))
      ((Category.comp_id _).trans (Category.id_comp _).symm) (pt _ _ hc).symm
    rw [← MonObj.comp_mul] at m
    exact m.symm
  · exact pt _ _ hc
  · exact pt _ _ he
end GlobalTheory.TwistLoc
