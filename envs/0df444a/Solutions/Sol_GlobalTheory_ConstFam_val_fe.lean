-- Prove2me | solution 1 for GlobalTheory.ConstFam.val_fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:12.374986+00:00
-- url     : https://prove2.me/submissions/288d9bc3-552d-468b-8f9b-38dd63fd303a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_GlobalTheory_ConstFam_gen_unique_scal
import Theorems.Thm_GlobalTheory_ConstFam_toStk_eq
import Theorems.Thm_GlobalTheory_ConstFam_xUnit_zpow
import Theorems.Thm_GlobalTheory_ConstFam_val_psi
import Theorems.Thm_GlobalTheory_ConstFam_val_rig
import Theorems.Thm_GlobalTheory_ConstFam_val_tau
import Theorems.Thm_GlobalTheory_ConstFam_fe_alg
import Theorems.Thm_GlobalTheory_ConstFam_be_add_div_two
import Theorems.Thm_GlobalTheory_ConstFam_trF_prB
import Theorems.Thm_GlobalTheory_ConstFam_val_feGen
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_UUA_val_powGen__89687e20c37b
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_surj_appTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
include hW hG
namespace GlobalTheory.ConstFam
theorem _root_.solution (α mu : a.D₀.X)
    (u u' : LB.Gen (LB.LinComb P.toPre.P.L (DegPre.deltaφ P.toPre F j (e α) (e mu)) (DegPre.deltaε j)))
    (hu : u.IsGen) (hc : LB.Gen.Corr P.toPre.P.L _ _ _ _ (LB.pullGen P.toPre.P.L _ _ u (DegPre.zF P.toPre F).left)
      (DegPre.famMult P.toPre F j (e mu) (e α))) (hu' : u'.IsGen)
    (hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF P.toPre F).left) (z : Z) J₀ J, Good a.D₀.P.L z J₀ →
      Good P.toPre.P.L z J → val (feGen a.D₀ j mu α) (r ≫ (DegPre.prB P.toPre F).left ≫ φ) z J₀ =
        (∏ i, wVal w z J₀ J (r ≫ DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i) * val u' r z J)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF P.toPre F).left) {z : Z} {J} (hJ : Good P.toPre.P.L z J) :
    (val u r z J).val = constVal (r ≫ strF P.toPre F) z
      (toF (R := PowerSeries k) F PowerSeries.X ^ expo a j α mu) * (val u' r z J).val := by
  let _ : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) (constF k F).injective).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x := fun x =>
    IsFractionRing.lift_algebraMap (constF k F).injective x
  have z₁ : DegPre.zF P.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF P.toPre F ≫ DegPre.prB P.toPre F = 1 := lift_snd _ _
  refine gen_unique_scal P.toPre.P.isLB (strF P.toPre F) (DegPre.zF P.toPre F).left (congrArg (fun q => q.left) z₁)
    (surj_appTop P.toPre F hG) hu hu' _ (fun y J hJ => ?_) Z r z J hJ
  obtain ⟨J₀, hJ₀⟩ := exists_good' a.D₀.P.isLB y
  let κ : Over.mk ((TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k))) ⟶ TK k :=
    Over.homMk (jFK (R := k) F) (by
      show (TF (R := k) F).hom = (TF (R := PowerSeries k) F).hom ≫ _
      rw [TF_hom, TF_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hF))
  have C : IsCub (th a.D₀ (T := Over.mk ((TF (R := PowerSeries k) F).hom ≫ spMap (PowerSeries.C (R := k)))) y J₀) :=
    isCub_cubV a.D₀.cub hJ₀
  have v₀ := val_feGen a.D₀ j mu α (pushHom hW.1 (TF (R := PowerSeries k) F) 1) κ hJ₀
  have p₀ : (DegPre.zF P.toPre F).left ≫ (DegPre.prB P.toPre F).left ≫ φ =
      (pushHom hW.1 (TF (R := PowerSeries k) F) 1).left := by
    rw [← Category.assoc, ← Over.comp_left, z₂]; rfl
  have v₁ := hv _ (DegPre.zF P.toPre F).left y J₀ J hJ₀ hJ
  rw [p₀] at v₁
  replace v₁ := v₀.symm.trans v₁
  rw [map_one, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul, val_tau _ _ hJ₀] at v₁
  have p₁ := prod_fam P.toPre F (DegPre.zF P.toPre F) (e α + j • e mu) j (wVal w y J₀ J)
  have p₂ := prod_fam P.toPre F (DegPre.zF P.toPre F ≫ DegPre.trF P.toPre F (e mu)) (e α) j (wVal w y J₀ J)
  have p₃ : (DegPre.zF P.toPre F ≫ DegPre.trF P.toPre F (e mu)) ≫ DegPre.prB P.toPre F = cP P.toPre _ (e mu) := by
    rw [Category.assoc, trF_prB, ← Category.assoc, z₂, MonObj.comp_mul, comp_cP, Category.comp_id, _root_.one_mul]
  rw [z₂, _root_.mul_one] at p₁
  rw [p₃] at p₂
  simp only [Over.comp_left, Category.assoc] at p₂
  have p₄ := prod_sum₂ (K := Fin 4) (K' := Fin 4) (fun i => wVal w y J₀ J ((DegPre.zF P.toPre F).left ≫
    DegPre.deltaφ P.toPre F j (e α) (e mu) i) ^ DegPre.deltaε j i) p₁ (prod_neg _ _ p₂)
  replace v₁ := v₁.trans (congrArg (· * _) p₄)
  have v₂ := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at v₂
  replace v₂ := v₂.trans (val_famMult (𝟙 (TF (R := PowerSeries k) F)) hJ j (e mu) (e α))
  rw [UUA.val_powGen', UUA.val_powGen', val_tau _ _ hJ, Over.id_left, Category.id_comp, ← map_add] at v₂
  have q₁ := val_psi hW F hF hJ₀ hJ (mu + α)
  have q₂ := val_psi hW F hF hJ₀ hJ mu
  have q₃ := val_psi hW F hF hJ₀ hJ α
  have q₄ := val_rig hW F hF hJ₀ hJ
  rw [be_add_div_two, map_add, cPoint_add, mul_comm (cP P.toPre _ (e mu)), ← map_add] at q₁
  refine Eq.trans ?_ (congrArg (· * _) ((xUnit_zpow F y _).trans (toStk_eq y _)))
  rw [← Units.val_mul]
  exact congrArg Units.val (fe_alg j _ _ _ v₁ v₂ q₁ q₂ q₃ q₄)
end GlobalTheory.ConstFam
