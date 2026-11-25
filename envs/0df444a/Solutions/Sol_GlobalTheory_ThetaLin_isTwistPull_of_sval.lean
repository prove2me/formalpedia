-- Prove2me | solution 1 for GlobalTheory.ThetaLin.isTwistPull_of_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:33:04.795314+00:00
-- url     : https://prove2.me/submissions/83e172a8-aaf3-4f44-a92e-aa34861b1501

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ThetaLin
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
  {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
  {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
namespace GlobalTheory.ThetaLin
theorem _root_.solution (hL : L.IsLB) (hα : α.IsGen) {s : LB.Sec (LPow A L b T)}
    {s' : LB.Sec (LPow A L a T)}
    (H : ∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y J = (val α (𝟙 _) y J).val * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y J) :
    IsTwistPull A L ψ m hm a b α s s' := by
  intro j
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have h0 := chart_le_zero A L m j hy
  have h1 := chart_le_pull A L ψ m hm j hy
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hy _) ((gs_res _ y _ hy _).trans
      (gs_pull _ ψ.left y _ h1 _)))).symm)
  refine (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y h0
    (Good.mem hJ _ _)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val (gen_trans hα (𝟙 _) y hy (Good.mem hJ _ _)))
    (sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) y h1
    (Good.mem hJ _ _))).symm
  refine (congrArg _ (H y J hJ)).trans ?_
  rw [Units.val_mul]
  refine Eq.trans ?_ (_root_.mul_mul_mul_comm _ _ _ _)
  rw [← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e' : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e]
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, zpow_neg]
  rw [e']
  exact (inv_mul_cancel_right _ _).symm
end GlobalTheory.ThetaLin
