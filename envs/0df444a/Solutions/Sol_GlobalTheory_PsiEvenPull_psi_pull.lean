-- Prove2me | solution 1 for GlobalTheory.PsiEvenPull.psi_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:44.249051+00:00
-- url     : https://prove2.me/submissions/e5e60b92-ff62-42e5-96cc-6ea537e006ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PsiEvenPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.PsiEvenPull
theorem _root_.solution (hD : IsPullDeg φ D D') (x : D'.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R').left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (hD.psiW.psi (hD.xe x)) (r ≫ hD.g) z J =
      (gw hD.w (r ≫ D'.xK x) z (J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))⁻¹ * val (D'.psi x) r z J' := by
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  have m₁ : r z ∈ D'.xK x ⁻¹ᵁ ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓
      D'.P.L.U (J' (r ≫ D'.xK x))) := ⟨mem_pull.2 (hJ ((r ≫ D'.xK x) ≫ proj hD)), hJ' (r ≫ D'.xK x)⟩
  have e₁ := congrArg (gm r z (D'.xK x ⁻¹ᵁ ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓
      D'.P.L.U (J' (r ≫ D'.xK x))))) (hb (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) (J' (r ≫ D'.xK x)))
  have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
      ((D.P.L.pull (proj hD)).U (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) ⊓ D'.P.L.U (J' (r ≫ D'.xK x))) m₁ _)))
      (gm_res _ z _ m₁ _))))
  refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcorr r).symm.trans ((val_of b r z J
    (fun _ => J ((r ≫ D'.xK x) ≫ proj hD)) (fun _ => by rw [Category.assoc])).trans (e₁'.trans ?_)))
  rw [zpow_neg_one]
  rfl
end GlobalTheory.PsiEvenPull
