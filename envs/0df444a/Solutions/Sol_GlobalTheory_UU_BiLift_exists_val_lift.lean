-- Prove2me | solution 1 for GlobalTheory.UU.BiLift.exists_val_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:29.977453+00:00
-- url     : https://prove2.me/submissions/9feaedc8-2d80-4631-a990-2e551832f0d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullLam
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GenLift_exists_genPull_eq
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_TorusCoord_IsPointOf_pull
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BiLift
variable {X Y Y₀ : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.UU.BiLift
theorem _root_.solution (hL : L.IsLB) (f : Y₀ ⟶ Y) [IsClosedImmersion f] [Surjective f] [IsAffine Y]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t₀ : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₀) (z : Z) (J), Good L z J → val t (r ≫ f) z J = val t₀ r z J := by
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull f).U j ≤ LB.wchart L (fun k => f ≫ φ k) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  let c : LB.Gen ((LB.LinComb L φ ε).pull f) := ⟨fun j => res (le j) (t₀.s (j PUnit.unit))⟩
  have hc : c.IsGen := isGen_of_gm (M := LB.LinComb L φ ε) c fun y j j' hj hj' => by
    refine (gm_res _ y _ hj _).trans ((gen_trans ht₀ (𝟙 Y₀) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) ?_ (gm_res _ y _ hj' _).symm))
    unfold trF
    symm
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_linComb L φ ε (𝟙 Y₀ ≫ f) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
    simp only [Category.assoc]
  obtain ⟨t, ht, e⟩ := GenLift.exists_genPull_eq f (LB.isLB_linComb hL φ ε) c hc
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  rw [val_of t (r ≫ f) z J (fun k => J (r ≫ f ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => f ≫ φ k) r
  have hm' : r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ k => J (r ≫ f ≫ φ k)) :=
    mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k)
  have e' := congrArg (fun q : LB.Gen ((LB.LinComb L φ ε).pull f) => gm r z _ (q.s fun _ k => J (r ≫ f ≫ φ k))) e
  refine Eq.trans ?_ (e'.trans (gm_res r z _ hm' _))
  exact ((gm_res r z _ hm' _).trans (gm_pull r f z _ (mem_pull.1 hm') _)).symm
end GlobalTheory.UU.BiLift
