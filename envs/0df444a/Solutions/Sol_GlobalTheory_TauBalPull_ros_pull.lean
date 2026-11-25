-- Prove2me | solution 1 for GlobalTheory.TauBalPull.ros_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:02:18.497422+00:00
-- url     : https://prove2.me/submissions/d763dadf-6da3-4eeb-afd8-8c31129487aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauBalPull_push_comp
import Theorems.Thm_GlobalTheory_TauBalPull_push_inj
import Theorems.Thm_P2M_GlobalTheory_TauBalPull_val__one_971f3d4236f4
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique__84c95b4ccdb0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_ros
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
namespace GlobalTheory.TauBalPull
theorem _root_.solution (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g]
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L))
    {T : Over (Sp R')} {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x y : T ⟶ D'.P.A) :
    val u (lift (pushPt (pull_grp hD).1.w x) (pushPt (pull_grp hD).1.w y)).left z J =
      (∏ i, gw hD.w ((lift x y).left ≫ rosatiφ D'.P.A f' g' i) z
        (J (((lift x y).left ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' ((lift x y).left ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' (lift x y).left z J' := by
  have gp := pull_grp hD
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ D'.P.A), pushPt gp.1.w (x * y) = pushPt gp.1.w x * pushPt gp.1.w y :=
    fun x y => map_mul (pushHom gp _) x y
  have p1 : ∀ {T : Over (Sp R')}, pushPt gp.1.w (1 : T ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff hD.w).1 hD.w_gen) D.P.isLB D'.P.isLB u' hu'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (D'.P.A ⊗ D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ i, gw hD.w (r ≫ rosatiφ D'.P.A f' g' i) z
        (J ((r ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' (r ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let m : (D'.P.A ⊗ D'.P.A).left ⟶ (D.P.A ⊗ D.P.A).left :=
    (lift (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A))).left
  have hm : ∀ {T : Over (Sp R')} (x y : T ⟶ D'.P.A),
      (lift x y).left ≫ m = (lift (pushPt gp.1.w x) (pushPt gp.1.w y)).left := fun {T} x y => by
    let ρ : Over.mk (T.hom ≫ spMap φ) ⟶ Over.mk ((D'.P.A ⊗ D'.P.A).hom ≫ spMap φ) :=
      Over.homMk (lift x y).left (by
        show (lift x y).left ≫ (D'.P.A ⊗ D'.P.A).hom ≫ spMap φ = T.hom ≫ spMap φ
        rw [← Category.assoc, Over.w])
    have r : ∀ q : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, ρ ≫ pushPt gp.1.w q = pushPt gp.1.w (lift x y ≫ q) := fun q =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    have : ρ ≫ lift (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A)) =
        lift (pushPt gp.1.w x) (pushPt gp.1.w y) := by rw [comp_lift, r, r, lift_fst, lift_snd]
    exact congrArg (fun q => q.left) this
  let e : 𝟙_ (Over (Sp R')) ⟶ D'.P.A ⊗ D'.P.A := lift 1 1
  have sj : Function.Surjective ((snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2
  have he : e.left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun i => m ≫ rosatiφ D.P.A f g i) (ε := rosatiε)
    (fun V _ k => by
      have p₁ := prod_ros f g (pushPt gp.1.w (fst D'.P.A D'.P.A)) (pushPt gp.1.w (snd D'.P.A D'.P.A)) k
      have p₂ := prod_ros f' g' (fst D'.P.A D'.P.A) (snd D'.P.A D'.P.A)
        (fun q => k (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
      rw [lift_fst_snd, Over.id_left] at p₂
      simp only [Category.id_comp] at p₂
      rw [← push_comp hD hf, ← push_comp hD hg, ← pm, ← pm] at p₁
      exact p₂.trans p₁.symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hu m) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have p := prod_ros f' g' (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1
        (fun q => gw hD.w q y (I (q ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (I' q))
      have f₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) ≫ f' = 1 :=
        push_inj hD (by rw [push_comp hD hf, p1, MonObj.one_comp])
      have g₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) ≫ g' = 1 :=
        push_inj hD (by rw [push_comp hD hg, p1, MonObj.one_comp])
      rw [f₁, g₁, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (val₂_one u' h₀' hI'))).symm
      refine (val_pull hI _ _ _).trans ?_
      rw [hm, p1]
      refine (val₂_one u h₀ (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).trans ?_
      simp) _ (lift x y).left z J hJ
  rw [← hm]
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))
end GlobalTheory.TauBalPull
