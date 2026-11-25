-- Prove2me | solution 1 for GlobalTheory.PhiPull.liftB_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:09.670802+00:00
-- url     : https://prove2.me/submissions/ee083b1b-543f-48c3-8b86-a37dff8b3db2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_GlobalTheory_PhiPull_liftB_fst
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pr
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (hD : IsPullDeg φ D D') (hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (hΘ₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (hΘ₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
include hΘ₂
namespace GlobalTheory.PhiPull
theorem _root_.solution (ρ : T' ⟶ DegPre.BF D' F) {b : TF (R := R) F ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = b.left) :
    liftB hT hΘ₁ ρ ≫ DegPre.trPt D F b = liftB hT hΘ₁ (ρ ≫ DegPre.trPt D' F b') := by
  apply CartesianMonoidalCategory.hom_ext
  · refine Over.OverMorphism.ext ?_
    rw [Category.assoc, tr_fst, liftB_fst, liftB_fst, Category.assoc, tr_fst]
  · refine Eq.trans ?_ (liftB_pr hD hT hΘ₁ hΘ₂ _).symm
    rw [Category.assoc, Category.assoc, tr_pr, tr_pr, MonObj.comp_mul, MonObj.comp_mul, map_mul,
      liftB_pr hD hT hΘ₁ hΘ₂, liftB_pt hD hT hΘ₁ ρ hb]
end GlobalTheory.PhiPull
