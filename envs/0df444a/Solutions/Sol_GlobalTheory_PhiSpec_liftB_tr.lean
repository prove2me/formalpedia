-- Prove2me | solution 1 for GlobalTheory.PhiSpec.liftB_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:16:26.756843+00:00
-- url     : https://prove2.me/submissions/2ec19b85-a56d-48e2-94a3-b225e05eccba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
import Theorems.Thm_GlobalTheory_PhiSpec_trT_fst
import Theorems.Thm_GlobalTheory_PhiSpec_trT_snd
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_fst
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_pr
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_pt
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
open GlobalTheory.PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
include hΘ₂
namespace GlobalTheory.PhiSpec
theorem _root_.solution (ρ : T' ⟶ DegPre.BF D' F) {b : T ⟶ D.P.A} {b' : TF (R := R') F ⟶ D'.P.A}
    (hb : b'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ b.left) :
    liftB hT hΘ₁ ρ ≫ trT D b = liftB hT hΘ₁ (ρ ≫ DegPre.trPt D' F b') := by
  apply CartesianMonoidalCategory.hom_ext
  · refine Over.OverMorphism.ext ?_
    rw [Category.assoc, trT_fst, liftB_fst, liftB_fst, Category.assoc ρ, tr_fst]
  · refine Eq.trans ?_ (liftB_pr hD hT hΘ₁ hΘ₂ _).symm
    rw [Category.assoc, Category.assoc, trT_snd, tr_pr, MonObj.comp_mul, MonObj.comp_mul, map_mul,
      liftB_pr hD hT hΘ₁ hΘ₂, liftB_pt hD hT hΘ₁ ρ hb]
end GlobalTheory.PhiSpec
