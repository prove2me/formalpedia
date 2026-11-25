-- Prove2me | solution 1 for GlobalTheory.PsiEvenPull.even_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:40.842194+00:00
-- url     : https://prove2.me/submissions/b2effac6-0203-49f0-8243-a27295d2798b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Theorems.Thm_GlobalTheory_PsiEvenPull_val_eq_of_app_injective
import Theorems.Thm_GlobalTheory_PsiEvenPull_c_neg
import Theorems.Thm_GlobalTheory_PsiEvenPull_app_injective_generic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
theorem _root_.solution (h : D.PsiEven) {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (χ : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (TW W).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val (ψW.psi (-χ)) r z J * val D.sym (r ≫ (toUnit (TW W) ≫ D.c χ).left) z J = val (ψW.psi χ) r z J := by
  have cn : (toUnit (TW W) ≫ D.c (-χ)).left = (toUnit (TW W) ≫ D.c χ).left ≫ (ι[D.P.A]).left := by
    rw [c_neg, ← Category.assoc, Over.comp_left]
  have key := val_eq_of_app_injective D.P.isLB (u' := LB.mulGen D.P.L _ _ _ _ (ψW.psi (-χ))
      (LB.pullGen D.P.L _ _ D.sym (toUnit (TW W) ≫ D.c χ).left)) (u := ψW.psi χ) (fun V _ k => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      show k (toUnit (TW W) ≫ D.c (-χ)).left ^ (-1 : ℤ) * (k ((toUnit (TW W) ≫ D.c χ).left ≫ (ι[D.P.A]).left) ^ (1 : ℤ) *
        k ((toUnit (TW W) ≫ D.c χ).left ≫ 𝟙 _) ^ (-1 : ℤ)) = k (toUnit (TW W) ≫ D.c χ).left ^ (-1 : ℤ)
      rw [cn, Category.comp_id]
      simp) (jK R ∣_ W) (app_injective_generic W) (ψW.psi_gen χ)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (fun y I hI => by
      have p : ∀ a, val (ψW.psi a) (jK R ∣_ W) y I = val (D.psi a) (jK R ⁻¹ᵁ W).ι y I := fun a => by
        have := val_corr hI (ψW.psi_eq a) (𝟙 _)
        rwa [val_pull hI, val_pull hI, Category.id_comp, Category.id_comp] at this
      have q : (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ D.xK χ := by
        show (jK R ∣_ W) ≫ W.ι ≫ (D.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D.c χ).left
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      have e := val_corr hI (h χ) (jK R ⁻¹ᵁ W).ι
      rw [val_mul hI, val_pull hI] at e
      rw [val_mul hI, val_pull hI, p, p, q]
      exact e.symm) Z r z J hJ
  rw [val_mul hJ, val_pull hJ] at key
  exact key.symm
end GlobalTheory.PsiEvenPull
