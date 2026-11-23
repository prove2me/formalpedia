-- Prove2me | solution 1 for GlobalTheory.ThetaPtExist.exists_isTwistPull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:13.145447+00:00
-- url     : https://prove2.me/submissions/c05b2736-2534-4f80-afcf-9fb73c3c38c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
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
open GlobalTheory GlobalTheory.ThetaPtExist
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.ThetaPtExist
theorem _root_.solution (hL : L.IsLB) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (hα : α.IsGen)
    (s : LB.Sec (LPow A L b T)) : ∃ s', IsTwistPull A L ψ m hm a b α s s' := by
  have e₀ : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hw⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, e₀]
      rw [_root_.mul_comm, inv_mul_cancel_right])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left
      (φ₃ := ![(snd T A).left, m.left]) (ε₃ := ![a, -b]) α hα)
  refine ⟨s', fun j => fn_ext fun y hy => ?_⟩
  have e : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, e₀]
  refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hy _)
      ((gs_res _ y _ hy _).trans (gs_pull (𝟙 _) ψ.left y
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
        (chart_le_pull A L ψ m hm j hy) _)))).symm)
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  have a₁ := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) y
    (chart_le_zero A L m j hy) (hJ'.mem _ _)
  have a₂ := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s
    (𝟙 _ ≫ ψ.left) y (chart_le_pull A L ψ m hm j hy) (hJ'.mem _ _)
  have a₃ := gen_trans (φ := ![(snd T A).left, m.left]) (ε := ![a, -b]) hα (𝟙 _) y hy (hJ'.mem _ _)
  have a₄ : trF (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _) y (fun _ => j 0)
        (fun _ => J (𝟙 _ ≫ (snd T A).left)) =
      trF ![(snd T A).left, m.left] ![a, -b] (𝟙 _) y j
        (fun i => J (𝟙 _ ≫ ![(snd T A).left, m.left] i)) *
      trF (fun _ : Fin 1 => (snd T A).left) (fun _ => b) (𝟙 _ ≫ ψ.left) y (fun _ => j 1)
        (fun _ => J ((𝟙 _ ≫ ψ.left) ≫ (snd T A).left)) := by
    rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
    have h : ∀ u w : ((T ⊗ A).left.presheaf.stalk y)ˣ, u ^ a = u ^ a * w ^ (-b) * w ^ b := fun u w => by
      rw [zpow_neg, inv_mul_cancel_right]
    exact h _ _
  refine a₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val a₃) a₂).symm)
  rw [a₄, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
  exact congrArg (_ * ·) ((hw _ _ y J hJ').trans ((sval_pullMulSec _ _ _ _ _ y hJ').trans (_root_.mul_comm _ _)))
end GlobalTheory.ThetaPtExist
