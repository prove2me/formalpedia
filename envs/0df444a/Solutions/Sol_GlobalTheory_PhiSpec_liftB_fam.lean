-- Prove2me | solution 1 for GlobalTheory.PhiSpec.liftB_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:33.464192+00:00
-- url     : https://prove2.me/submissions/aec5fa44-cbd1-40fe-8d79-2f72d3b74931

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
import Theorems.Thm_GlobalTheory_PhiSpec_liftB_pr
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pr
import Theorems.Thm_GlobalTheory_PhiPull_push_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
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
theorem _root_.solution (ρ : T' ⟶ DegPre.BF D' F) (x : D'.X) (κ : Fin 4) :
    (liftB hT hΘ₁ ρ).left ≫ (snd T D.P.A).left ≫ D.famφB (hD.xe x) κ =
      (ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  fin_cases κ
  · exact (congrArg ((liftB hT hΘ₁ ρ).left ≫ ·) (Category.comp_id _)).trans
      (congrArg (fun q => q.left) (liftB_pr hD hT hΘ₁ hΘ₂ ρ))
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ (𝟙 D.P.A * cP D _ (hD.xe x)) =
        pushHom (pull_grp hD) T' (ρ ≫ (DegPre.prB D' F * cP D' _ x)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, map_mul, comp_cP, comp_cP, comp_cP, PhiPull.push_cP,
        Category.comp_id, liftB_pr hD hT hΘ₁ hΘ₂]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ cP D _ (hD.xe x) = pushHom (pull_grp hD) T' (ρ ≫ cP D' _ x) := by
      rw [comp_cP, comp_cP, comp_cP, PhiPull.push_cP]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ snd T D.P.A ≫ (1 : D.P.A ⟶ D.P.A) =
        pushHom (pull_grp hD) T' (ρ ≫ (1 : DegPre.BF D' F ⟶ D'.P.A)) := by
      rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, map_one]
    exact congrArg (fun q => q.left) e
end GlobalTheory.PhiSpec
