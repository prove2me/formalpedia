-- Prove2me | solution 1 for GlobalTheory.ThetaAct.isActOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:41.45061+00:00
-- url     : https://prove2.me/submissions/5277cce9-b0a9-406f-99fa-f3dc6491b9cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Theorems.Thm_GlobalTheory_ThetaAct_translT_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaAct
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaAct
theorem _root_.solution (hL : L.IsLB) (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)) :
    IsActOf A L k θ s s' ↔ ∀ y J, Good L y J → sv (SecM.ofSec A s') (𝟙 _) y J =
      (tval θ (𝟙 _) y J).val * sv (SecM.ofSec A s) (𝟙 _ ≫ (translT A θ.pt).left) y J := by
  have key : ∀ (j : Fin 2 → L.ι) (y : (T ⊗ A).left)
      (hy : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j),
      gs (𝟙 _) y _ (((T ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L (translPt A θ.pt) j)).op).hom
        (s'.f (fun _ => j 0))) =
        gs (𝟙 _) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) ∧
      gs (𝟙 _) y _ ((show Γ((T ⊗ A).left, LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) from
        (θ.φ.s j).val) * ((T ⊗ A).left.presheaf.map (homOfLE
          (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j)).op).hom
          (((translT A θ.pt).left.app _).hom (s.f (fun _ => j 1)))) =
        (gm (𝟙 _) y (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) (θ.φ.s j)).val *
          gs (𝟙 _ ≫ (translT A θ.pt).left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j y hy =>
    ⟨gs_res _ y _ hy _, (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hy _)
      ((gs_res _ y _ hy _).trans (gs_pull (𝟙 _) (translT A θ.pt).left y
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
        (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j hy) _)))⟩
  have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left = 𝟙 _ ≫ (translPt A θ.pt).left := by
    rw [Category.assoc, translT_snd]
  constructor
  · intro H y J hJ
    have hm := hJ.mem ![(snd T A).left, (translPt A θ.pt).left] (𝟙 _)
    obtain ⟨k₁, k₂⟩ := key _ y hm
    have := k₁.symm.trans ((congrArg (gs (𝟙 _) y _) (H _)).trans k₂)
    refine this.trans (congrArg (_ * ·) (Eq.symm ?_))
    exact sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s _ y J _ (fun _ => congrArg J e)
  · intro H j
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := key j y hy
    refine k₁.trans (Eq.trans ?_ k₂.symm)
    choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    have a₁ := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y
      (chart_le_zero A L (translPt A θ.pt) j hy) (hJ'.mem _ _)
    have a₂ := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s
      (𝟙 _ ≫ (translT A θ.pt).left) y
      (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j hy) (hJ'.mem _ _)
    have a₃ := gen_trans (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.isGen (𝟙 _) y hy
      (hJ'.mem _ _)
    have a₄ : trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) y (fun _ => j 0)
          (fun _ => J (𝟙 _ ≫ (snd T A).left)) =
        trF ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) y j
          (fun i => J (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) *
        trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) y (fun _ => j 1)
          (fun _ => J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)) := by
      rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
      have h : ∀ a b : ((T ⊗ A).left.presheaf.stalk y)ˣ, a ^ k = a ^ k * b ^ (-k) * b ^ k := fun a b => by
        rw [zpow_neg, inv_mul_cancel_right]
      exact h _ _
    refine a₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val a₃) a₂).symm)
    rw [a₄, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
    exact congrArg (_ * ·) (H y J hJ')
end GlobalTheory.ThetaAct
