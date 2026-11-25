-- Prove2me | solution 1 for GlobalTheory.CubeLift.exists_pmaps_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:51:01.299099+00:00
-- url     : https://prove2.me/submissions/1fd2ae31-58d9-4a86-ba82-f07565c45a41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq
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
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
namespace GlobalTheory.CubeLift
theorem _root_.solution {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (h : Y' ⟶ Y) [IsClosedImmersion h] [Surjective h] [IsAffine Y] (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧ PMaps w φ' φ ε a t h := by
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U j ≤
      LB.wchart L (fun k => φ' k ≫ F) (j PUnit.unit) := fun j y hy => Set.mem_iInter.2 fun k => by
    have : φ k (h y) ∈ L.U (j PUnit.unit k) := Set.mem_iInter.1 (mem_pull.1 hy) k
    rw [pt_eq hc] at this
    exact this
  let t₀ : LB.Gen ((LB.LinComb L φ ε).pull h) := ⟨fun j => res (le j) (t₁.s (j PUnit.unit))⟩
  have ht₀ : t₀.IsGen := isGen_of_gm _ fun y j j' hj hj' => by
    refine (gm_res (𝟙 Y') y (le j) hj _).trans ((gen_trans ht₁ (𝟙 Y') y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y') y (le j') hj' _).symm))
    unfold trF
    symm
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
    simp only [hc, Category.assoc]
  obtain ⟨t, ht, e⟩ := GenLift.exists_genPull_eq h (LB.isLB_linComb hL φ ε) t₀ ht₀
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  have m : h (r z) ∈ LB.wchart L φ p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  have m' : r z ∈ ((LB.LinComb L φ ε).pull h).U fun _ => p := mem_pull.2 m
  refine Eq.trans ?_ (hv Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq))
  refine Eq.trans ?_ (gm_res r z (le fun _ => p) m' _)
  refine Eq.trans ?_ (congrArg (fun s : LB.Gen ((LB.LinComb L φ ε).pull h) => gm r z _ (s.s fun _ => p)) e)
  exact ((gm_res r z _ m' _).trans (gm_pull r h z _ m _)).symm
end GlobalTheory.CubeLift
