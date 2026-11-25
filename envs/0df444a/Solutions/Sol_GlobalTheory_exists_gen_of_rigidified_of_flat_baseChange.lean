-- Prove2me | solution 1 for GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:16:16.777924+00:00
-- url     : https://prove2.me/submissions/d93a49ed-dd75-4413-9f7a-7c0ca8477734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigidifiedFaithfullyFlatDescent
import Theorems.Thm_GlobalTheory_exists_gen_of_pull_id
import Theorems.Thm_GlobalTheory_CubeDescent_exists_gen_descend
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory
private theorem val_mul_val_comm_of_fst_eq (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) (A : Over S) [GrpObj A]
    (N : LB A.left) (hA : IsAbelianScheme A) (hN : N.IsLB)
    (w : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen) (hw : w.IsGen)
    (e' : S' ⟶ pullback A.hom π) (he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A)
    (he'q : e' ≫ pullback.snd A.hom π = 𝟙 S')
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ pullback A.hom π)
    (hg : g₁ ≫ pullback.fst A.hom π = g₂ ≫ pullback.fst A.hom π) (z : Z) (J : (Z ⟶ A.left) → N.ι)
    (hJ : Good N z J) :
    val w g₁ z J * val w (g₂ ≫ pullback.snd A.hom π ≫ e') z J =
      val w g₂ z J * val w (g₁ ≫ pullback.snd A.hom π ≫ e') z J := by
  have hπ : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
  let FinalForm : Over S := Over.mk (g₁ ≫ pullback.snd A.hom π ≫ π)
  have hw1 : (fst A FinalForm).left ≫ A.hom = (snd A FinalForm).left ≫ (g₁ ≫ pullback.snd A.hom π ≫ π) :=
    (Over.w (fst A FinalForm)).trans (Over.w (snd A FinalForm)).symm
  let a : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₁ ≫ pullback.snd A.hom π) (by rw [hw1]; simp)
  let a' : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₂ ≫ pullback.snd A.hom π) (by rw [hw1, hπ]; simp)
  let p0 : (A ⊗ FinalForm).left ⟶ Z := (snd A FinalForm).left
  let e : Z ⟶ (A ⊗ FinalForm).left := (lift (toUnit FinalForm ≫ η[A]) (𝟙 FinalForm)).left
  have he : e ≫ p0 = 𝟙 Z := by
    simp only [e, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hap : a ≫ pullback.fst A.hom π = a' ≫ pullback.fst A.hom π := by
    simp only [a, a']
    rw [pullback.lift_fst, pullback.lift_fst]
  have hU : (toUnit FinalForm).left = g₁ ≫ pullback.snd A.hom π ≫ π :=
    (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
  have hea : e ≫ a = g₁ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a, e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU]
      rfl
    · simp only [a, e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have hea' : e ≫ a' = g₂ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a', e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU, hπ]
      rfl
    · simp only [a', e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  let x : FinalForm ⟶ A := Over.homMk (g₁ ≫ pullback.fst A.hom π) (by simp [FinalForm, pullback.condition])
  let ρ : Z ⟶ (A ⊗ FinalForm).left := (lift x (𝟙 FinalForm)).left
  have hρp : ρ ≫ p0 = 𝟙 Z := by
    simp only [ρ, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hρa : ρ ≫ a = g₁ := by
    apply pullback.hom_ext
    · simp only [a, ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst]
      rfl
    · simp only [a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  have hρa' : ρ ≫ a' = g₂ := by
    apply pullback.hom_ext
    · simp only [a', ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst, ← hg]
      rfl
    · simp only [a', Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  let u := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a) (LB.pullGen N _ _ w (p0 ≫ e ≫ a'))
  let u' := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a') (LB.pullGen N _ _ w (p0 ≫ e ≫ a))
  have hu : u.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hu' : u'.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a') (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hF : FormEq (Sum.elim (fun _ : PUnit.{1} => a' ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a) ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1))
      (Sum.elim (fun _ : PUnit.{1} => a ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a') ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1)) := by
    intro U _ h
    simp [Fintype.prod_sum_type, hap]
  have key := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_unique' hN hF p0 e he
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_snd hG hA FinalForm) hu hu' ?_ Z ρ z J hJ
  · simp only [u, u'] at key
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
    have hρp' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), ρ ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, hρp, Category.id_comp]
    rw [hρp', hρp', hea', hea, hρa, hρa'] at key
    exact key
  · intro y J' hJ'
    simp only [u, u']
    rw [val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
    have he' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), e ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, he, Category.id_comp]
    rw [he', he', mul_comm]
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG S S' π A _ N hA hN hfl hsu hqc hr hw
  obtain ⟨r, hr⟩ := hr
  obtain ⟨w, hw⟩ := hw
  have := hfl
  have := hsu
  have := hqc
  have hz : (π ≫ eSec A) ≫ A.hom = 𝟙 S' ≫ π := by
    rw [Category.assoc, Category.id_comp]
    have h0 : (η[A]).left ≫ A.hom = 𝟙 S := Over.w (η[A])
    unfold eSec
    rw [h0, Category.comp_id]
  let e' : S' ⟶ pullback A.hom π := pullback.lift (π ≫ eSec A) (𝟙 S') hz
  have he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A := pullback.lift_fst _ _ _
  have he'q : e' ≫ pullback.snd A.hom π = 𝟙 S' := pullback.lift_snd _ _ _
  let w' : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen := w
  have hw' : w'.IsGen := hw
  let r' : (N.LinComb (fun _ : PUnit.{1} => eSec A) (fun _ => (1 : ℤ))).Gen := r
  have hr' : r'.IsGen := hr
  let v := LB.mulGen N _ _ _ _ w' (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ r' (pullback.snd A.hom π ≫ π))
    (LB.invGen N _ _ (LB.pullGen N _ _ w' (pullback.snd A.hom π ≫ e'))))
  have hv : v.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ hw'
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ r' hr' _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w' hw' _)))
  obtain ⟨t', ht', hvv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := fun _ : PUnit.{1} => pullback.fst A.hom π ≫ 𝟙 A.left) (ε' := fun _ => (1 : ℤ))
    (by intro U _ h; simp [Fintype.prod_sum_type, he'p]) v hv
  refine Exists.elim (GlobalTheory.CubeDescent.exists_gen_descend hN (pullback.fst A.hom π)
    (fun _ : PUnit.{1} => 𝟙 A.left) (fun _ => (1 : ℤ)) t' ht' ?_) (fun t ht => exists_gen_of_pull_id N t ht)
  · intro Z g₁ g₂ z J hJ hg
    rw [hvv Z g₁ z J hJ, hvv Z g₂ z J hJ]
    simp only [v, val_mul hJ, val_pull hJ, val_inv]
    have hq : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
      rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
    rw [hq]
    have key := val_mul_val_comm_of_fst_eq hG π A N hA hN w' hw' e' he'p he'q g₁ g₂ hg z J hJ
    rw [mul_left_comm (val w' g₁ z J), mul_left_comm (val w' g₂ z J)]
    congr 1
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact key
end GlobalTheory
