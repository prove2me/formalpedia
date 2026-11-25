-- Prove2me | solution 1 for GlobalTheory.RosatiCube.ros_sum_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:11.95382+00:00
-- url     : https://prove2.me/submissions/693d9b54-489f-4992-8bf6-bad0d1b3d2db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
import Theorems.Thm_GlobalTheory_RosatiCube_IsNormGen_val_origin
import Theorems.Thm_GlobalTheory_RosatiCube_val_pull_pair
import Theorems.Thm_GlobalTheory_RosatiCube_pair_unique_of_surj
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RosatiCube
open ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : LB A.left}
variable {Lr : RigLB A} (c : CubicalStr A Lr)
namespace GlobalTheory.RosatiCube
theorem _root_.solution (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) {f g f₁ g₁ f₂ g₂ : A ⟶ A}
    (hf : f = f₁ * f₂) (hg : g = g₁ * g₂) {u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsNormGen Lr.L f g u) (hu₁ : IsNormGen Lr.L f₁ g₁ u₁) (hu₂ : IsNormGen Lr.L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x w : T ⟶ A) :
    val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) =
      cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := by
  subst hf hg
  have ev : ∀ {T : Over S} {z : T.left} {J}, Good Lr.L z J → ∀ x w : T ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (lift (fst A A) (snd A A)).left)
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (snd A A ≫ g₁) (snd A A ≫ g₂))).left))
        (lift x w).left z J = val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) ∧
      val (LB.mulGen Lr.L _ _ _ _
        (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left)
        (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (lift (fst A A) (snd A A)).left)
          (LB.pullGen Lr.L _ _ u₂ (lift (fst A A) (snd A A)).left))) (lift x w).left z J =
        cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := fun hJ x w =>
    ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull_pair u _ hJ _ _) (val_cub c _ hJ _ _ _))).trans (by
      rw [lift_snd_assoc, lift_snd_assoc, lift_fst, lift_snd]),
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull_pair u₁ _ hJ _ _) (val_pull_pair u₂ _ hJ _ _))))).trans (by
      rw [lift_fst_assoc, lift_fst_assoc, lift_fst, lift_snd])⟩
  refine (ev hJ x w).1.symm.trans (Eq.trans (pair_unique_of_surj sj Lr.isLB (fun U _ h => ?_)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ c.isGen _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _)
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu₁.1 _) (pullGen_isGen _ _ _ _ hu₂.1 _)))
    (fun y I hI => ?_) _ hJ) (ev hJ x w).2)
  · refine (prod_sum₂ (K := thK) (K' := Fin 6 ⊕ Fin 6) (U := U) _ (prod_cub _ _ _ h)
      (prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ (prod_ros _ _ _ _ h) (prod_ros _ _ _ _ h))).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 6) (K' := thK) (U := U) _ (prod_ros _ _ _ _ h) (prod_cub _ _ _ h)).symm)
    rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C : IsCub (cubV c y I) := isCub_cubV c hI
    refine (ev hI 1 1).1.trans (Eq.trans ?_ (ev hI 1 1).2.symm)
    rw [hu.val_origin hI, hu₁.val_origin hI, hu₂.val_origin hI, C.face, C.face₃, _root_.mul_one, _root_.mul_one]
end GlobalTheory.RosatiCube
