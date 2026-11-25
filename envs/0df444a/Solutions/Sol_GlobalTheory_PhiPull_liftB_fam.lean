-- Prove2me | solution 1 for GlobalTheory.PhiPull.liftB_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:08:35.592366+00:00
-- url     : https://prove2.me/submissions/05f23bf7-182d-417b-b4a6-8831a29df3de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_GlobalTheory_PhiPull_push_cP
import Theorems.Thm_GlobalTheory_PhiPull_liftB_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP


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
theorem _root_.solution (ρ : T' ⟶ DegPre.BF D' F) (x : D'.X) (κ : Fin 4) :
    (liftB hT hΘ₁ ρ).left ≫ DegPre.famφ D F (hD.xe x) κ = (ρ.left ≫ DegPre.famφ D' F x κ) ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  fin_cases κ
  · exact congrArg (fun q => q.left) (liftB_pr hD hT hΘ₁ hΘ₂ ρ)
  · have e : liftB hT hΘ₁ ρ ≫ (DegPre.prB D F * cP D _ (hD.xe x)) =
        pushHom (pull_grp hD) T' (ρ ≫ (DegPre.prB D' F * cP D' _ x)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, map_mul, comp_cP, comp_cP, push_cP, liftB_pr hD hT hΘ₁ hΘ₂]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ cP D _ (hD.xe x) = pushHom (pull_grp hD) T' (ρ ≫ cP D' _ x) := by
      rw [comp_cP, comp_cP, push_cP]
    exact congrArg (fun q => q.left) e
  · have e : liftB hT hΘ₁ ρ ≫ (1 : DegPre.BF D F ⟶ D.P.A) =
        pushHom (pull_grp hD) T' (ρ ≫ (1 : DegPre.BF D' F ⟶ D'.P.A)) := by
      rw [MonObj.comp_one, MonObj.comp_one, map_one]
    exact congrArg (fun q => q.left) e
end GlobalTheory.PhiPull
