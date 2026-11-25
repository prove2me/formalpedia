-- Prove2me | solution 1 for GlobalTheory.PsiEvenPull.sym_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:52:03.902183+00:00
-- url     : https://prove2.me/submissions/669531f8-538f-4932-86c8-0042d7de618c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Theorems.Thm_GlobalTheory_PsiEvenPull_inv_proj
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
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
theorem _root_.solution (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ proj hD) z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw hD.w (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw hD.w r z (J (r ≫ proj hD)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw hD.w (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ proj hD)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw hD.w (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ proj hD)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => proj hD ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ proj hD) ^ (1 : ℤ) * k (𝟙 _ ≫ proj hD) ^ (-1 : ℤ) =
        k (proj hD ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (proj hD ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_proj, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen (proj hD)) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of R')))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (specOf φ)
      rw [val_pull hI, val_one, ← hD.he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))
end GlobalTheory.PsiEvenPull
