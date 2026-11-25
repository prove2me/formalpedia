-- Prove2me | solution 1 for GlobalTheory.PsiRing.val_sym_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:28:49.597005+00:00
-- url     : https://prove2.me/submissions/3c0e7c87-5d16-4e07-9b70-22b6b5aaca81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiEvenDescendBaseChange
import Theorems.Thm_GlobalTheory_PsiRing_inv_comp_of_isGrpPullback
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory GlobalTheory.PsiRing
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}
namespace GlobalTheory.PsiRing
theorem _root_.solution (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hv₀ : v.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ β) z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := by
  have he : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hv₀) D.P.isLB D'.P.isLB D'.sym D'.sym_gen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    show gw v (r ≫ (ι[D'.P.A]).left) z (J (r ≫ (ι[D'.P.A]).left ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) ^ (1 : ℤ) *
      gw v (r ≫ 𝟙 _) z (J (r ≫ 𝟙 _ ≫ β)) (J' (r ≫ 𝟙 _)) ^ (-1 : ℤ) = _
    rw [Category.comp_id, Category.id_comp, Category.assoc r, zpow_one, zpow_neg_one]
  have oi : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    have : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A] := by simp
    exact congrArg (fun q => q.left) this
  have key := gen_unique' D.P.isLB
    (φ := fun k => β ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) (ε := ![1, -1])
    (fun V _ k => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two]
      show k ((ι[D'.P.A]).left ≫ β) ^ (1 : ℤ) * k (𝟙 _ ≫ β) ^ (-1 : ℤ) =
        k (β ≫ (ι[D.P.A]).left) ^ (1 : ℤ) * k (β ≫ 𝟙 _) ^ (-1 : ℤ)
      rw [inv_comp_of_isGrpPullback gp, Category.id_comp, Category.comp_id])
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (DVR.pullGen_isGen _ _ _ _ D.sym_gen β) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Spec (CommRingCat.of V)))).left ⟶ D'.P.A.left =>
        exists_chart D'.P.isLB (χ y)
      have a := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', val_one, Category.id_comp] at a
      have b := val_corr hI D.sym_rig (spMap φ)
      rw [val_pull hI, val_one, ← he] at b
      refine ((val_pull hI _ _ _).trans b).trans (Eq.symm ((hv' _ _ y I I' hI hI').trans ?_))
      rw [a, oi, mul_inv_cancel, _root_.one_mul]) Z r z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))
end GlobalTheory.PsiRing
