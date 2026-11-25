-- Prove2me | solution 1 for GlobalTheory.PsiEvenPull.psiEven_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:05.08151+00:00
-- url     : https://prove2.me/submissions/b96fe0ac-51f4-46b0-a390-daf4dd82b8ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Theorems.Thm_GlobalTheory_PsiEvenPull_c_neg
import Theorems.Thm_GlobalTheory_PsiEvenPull_even_on
import Theorems.Thm_GlobalTheory_PsiEvenPull_sym_pull
import Theorems.Thm_GlobalTheory_PsiEvenPull_psi_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
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
theorem _root_.solution : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), D.PsiEven → D'.PsiEven := by
  intro hG R R' _ _ _ _ φ D D' hD h x
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have cW : hD.g ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ proj hD := by
    have hx : D'.xK x ≫ proj hD = jK R' ≫ specOf φ ≫ (D.c (hD.xe x)).left := by
      rw [← hD.c_pr x, ← Category.assoc]; rfl
    rw [hx, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [c_neg, ← Category.assoc, Over.comp_left]
  have e := even_on h hD.psiW (hD.xe x) (𝟙 _ ≫ hD.g) y J hJ
  rw [← map_neg, psi_pull hD _ _ y hJ hJ', psi_pull hD _ _ y hJ hJ', Category.assoc (𝟙 _) hD.g, cW,
    ← Category.assoc (𝟙 _) (D'.xK x), sym_pull hG hD _ y hJ hJ'] at e
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  rw [c'] at e
  rw [val_mul hJ', val_pull hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'
end GlobalTheory.PsiEvenPull
