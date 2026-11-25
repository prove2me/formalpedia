-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.exists_theta_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:07.579025+00:00
-- url     : https://prove2.me/submissions/fe9fb842-d392-4940-8927-5c5f98d598cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Theorems.Thm_GlobalTheory_ExpTrans_gen_val
import Theorems.Thm_GlobalTheory_ExpTrans_sec_val
import Theorems.Thm_GlobalTheory_ThetaAct_isActOf_iff
import Theorems.Thm_GlobalTheory_ThetaBaseChange_actVal_of_isActOf
import Theorems.Thm_GlobalTheory_ThetaScalar_translT_snd_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_theta_move
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_transl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S₁} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ)
    {ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left} (hψ : ψ = (psiO hp τ hτ).left) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ ∀ (s₀ s₀' : LB.Sec (LPow G L₀ k T₀)) (s s' : LB.Sec (LPow A L₁ k T)),
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s s₀ →
      PSec w (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T₀ G).left) (fun _ => k) ψ s' s₀' →
      IsActOf G L₀ k θ₀ s₀ s₀' → IsActOf A L₁ k θ s s' := by
  obtain ⟨θ, rfl, hm⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  have hm : PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
      θ.φ θ₀.φ ψ := hψ ▸ hm
  have c₁ : (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := hψ ▸ (psi_snd hp τ hτ).symm
  have c₂ : (translPt A θ.pt).left ≫ φ = ψ ≫ (translPt G θ₀.pt).left := hψ ▸ (psi_tr hp τ hτ _ _ hx).symm
  have c₃ : (translT A θ.pt).left ≫ ψ = ψ ≫ (translT G θ₀.pt).left := hψ ▸ psi_transl hp τ hτ _ _ hx
  refine ⟨θ, rfl, fun s₀ s₀' s s' m m' H => (ThetaAct.isActOf_iff hL₁ θ s s').2 fun y J hJ => ?_⟩
  choose J₀ hJ₀ using fun χ : (T ⊗ A).left ⟶ G.left => exists_chart hL₀ (χ y)
  have hJ₀ : Good L₀ y J₀ := hJ₀
  have c : ∀ _ : Fin 1, (snd T A).left ≫ φ = ψ ≫ (snd T₀ G).left := fun _ => c₁
  have a := actVal_of_isActOf H _ (𝟙 _ ≫ ψ) y J₀ hJ₀
  have b := ExpTrans.gen_val w _ _ _ _ (fun i => by
    fin_cases i
    · exact c₁
    · exact c₂) _ _ hm y hJ₀ hJ
  have d := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _) y (m' _ (𝟙 _) y) hJ₀ hJ
  have e := ExpTrans.sec_val w _ _ _ _ c _ _ (𝟙 _ ≫ (translT A θ.pt).left) y (m _ _ y) hJ₀ hJ
  have g : (𝟙 _ ≫ ψ) ≫ (translT G θ₀.pt).left =
      (𝟙 _ ≫ (translT A θ.pt).left) ≫ ψ := by
    rw [Category.assoc, Category.assoc, c₃]
  rw [g] at a
  rw [Fin.prod_univ_one] at d e
  rw [Fin.prod_univ_two] at b
  rw [Category.assoc _ _ (snd T A).left, translT_snd_left, Category.id_comp (translPt A θ.pt).left] at e
  rw [Category.id_comp (snd T A).left] at d
  have b' : thetaVal θ₀ (𝟙 _ ≫ ψ) y J₀ = ExpTrans.om w y J₀ J (snd T A).left ^ k *
      ExpTrans.om w y J₀ J (translPt A θ.pt).left ^ (-k) * thetaVal θ (𝟙 _) y J := by
    rw [Category.id_comp]; exact b
  have z := d.symm.trans (a.trans (congrArg₂ (· * ·) (congrArg Units.val b') e))
  refine (ExpTrans.om w y J₀ J (snd T A).left ^ k).mul_right_inj.1 (z.trans ?_)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, zpow_neg, mul_right_comm _ _⁻¹,
    inv_mul_cancel_right]
  rfl
end GlobalTheory.ThetaSpecialise
