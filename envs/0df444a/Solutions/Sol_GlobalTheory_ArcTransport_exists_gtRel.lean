-- Prove2me | solution 1 for GlobalTheory.ArcTransport.exists_gtRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:45:45.528515+00:00
-- url     : https://prove2.me/submissions/2d0bcf98-8282-4353-9af2-ebecf9e2c05f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_GlobalTheory_ArcTransport_exists_down_val
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_exists_good__b067f9275064
import Theorems.Thm_GlobalTheory_ArcTransport_vS_scale
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_surjective
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_cP
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_gt__push_64b33aecfb9b
import Theorems.Thm_GlobalTheory_ArcTransport_thS_push
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_iff
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scaleGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cPoint_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)
variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)
variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)
include gp hT hc hw
namespace GlobalTheory.ArcTransport
theorem _root_.solution (hG : GlobalFnsSt) (u : D.X → Fˣ) (hu : ∀ a b, u (a + b) = u a * u b) (g₀ : GtPtF D F) :
    ∃ g : GtPtF D' F, GtRel w e u g₀ g := by
  obtain ⟨b, hb⟩ := pushF_surjective gp hT g₀.b
  have u0 : u 0 = 1 := mul_eq_left.1 ((hu 0 0).symm.trans (congrArg u (add_zero 0)))
  have ex : ∀ χ, ∃ a : LB.Gen (LB.LinComb D'.P.L (DegPre.gtφ D' F b (e χ)) DegPre.gtε), a.IsGen ∧
      ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      (wVal w y J J' (cP D' _ (e χ) * b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' b *
        (wVal w y J J' 1)⁻¹ * vS (F := F) a y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by
    intro χ
    obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB (φ' := fun i => DegPre.gtφ D' F b (e χ) i ≫ Φ) (ε' := DegPre.gtε)
      (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i)
        (by rw [← hb]; exact (gtφ_push gp hT hc b χ i).symm))
      (scaleGen (unitTop (u χ)) (g₀.s χ)) (scaleGen_isGen _ _ (g₀.isGen χ))
    obtain ⟨a, ha, va⟩ := exists_down_val hw D.P.isLB D'.P.isLB t ht
    refine ⟨a, ha, fun y J J' hJ hJ' => ?_⟩
    have v₁ : vS a y J' = (pw (Y := Sp F) (Z := Sp F) w (DegPre.gtφ D' F b (e χ)) DegPre.gtε (𝟙 _) y
        (fun k => J (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k ≫ Φ)) (fun k => J' (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k)))⁻¹ *
        vS t y J := va y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have v₂ : vS t y J = unitStk y (u χ) * vS (g₀.s χ) y J := (vt _ _ y J hJ).trans (vS_scale _ _ hJ)
    have v₃ : pw (Y := Sp F) (Z := Sp F) w (DegPre.gtφ D' F b (e χ)) DegPre.gtε (𝟙 _) y
        (fun k => J (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k ≫ Φ)) (fun k => J' (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k)) =
        (wVal w y J J' (cP D' _ (e χ) * b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' b *
          (wVal w y J J' 1)⁻¹ := by
      refine Eq.trans ?_ (prod_gt b (e χ) (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q)))
      simp only [pw, Category.id_comp]
    rw [v₁, v₂, ← v₃]
    exact mul_inv_cancel_left _ _
  choose t ht vt using ex
  obtain ⟨g, hgb, hg⟩ := exists_gt b (fun χ => t (e.symm χ)) (fun χ => ht _) (fun χ U _ h =>
      Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i)
        (by rw [AddEquiv.apply_symm_apply])) (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
      have z : vS (g₀.s 0) y J = 1 := (val_corr hJ g₀.s_zero _).trans (val_one _)
      have v := vt 0 y J J' hJ hJ'
      show vS (t (e.symm 0)) y J' = 1
      rw [map_zero e.symm]
      rw [z, u0, map_one, _root_.mul_one, show cP D' (TF (R := R') F) (e 0) = 1 by rw [map_zero, cPoint_zero],
        _root_.one_mul] at v
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul v
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
      linear_combination (norm := abel) e') (fun χ χ' y J' hJ' => by
      obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
      obtain ⟨χ, rfl⟩ := e.surjective χ
      obtain ⟨χ', rfl⟩ := e.surjective χ'
      have e₀ := gt_mul (𝟙 (TF (R := R) F)) hJ g₀ χ χ'
      rw [Category.id_comp] at e₀
      have e₁ : vS (g₀.s (χ + χ')) y J * thS D y J (cP D _ χ) (cP D _ χ') g₀.b = vS (g₀.s χ) y J * vS (g₀.s χ') y J := e₀
      show vS (t (e.symm (e χ + e χ'))) y J' * thS D' y J' (cP D' _ (e χ)) (cP D' _ (e χ')) b =
        vS (t (e.symm (e χ))) y J' * vS (t (e.symm (e χ'))) y J'
      rw [← map_add, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      have c := thS_push gp hT hw hG hJ hJ' (cP D' _ (e χ)) (cP D' _ (e χ')) b
      rw [pushF_cP gp hT hc, pushF_cP gp hT hc, hb] at c
      rw [c] at e₁
      have v₁ := vt χ y J J' hJ hJ'
      have v₂ := vt χ' y J J' hJ hJ'
      have v₃ := vt (χ + χ') y J J' hJ hJ'
      rw [show cP D' (TF (R := R') F) (e (χ + χ')) = cP D' _ (e χ) * cP D' _ (e χ') by rw [map_add, cPoint_add], hu,
        map_mul] at v₃
      apply Additive.ofMul.injective
      have a₁ := congrArg Additive.ofMul e₁
      have b₁ := congrArg Additive.ofMul v₁
      have b₂ := congrArg Additive.ofMul v₂
      have b₃ := congrArg Additive.ofMul v₃
      simp only [ofMul_mul, ofMul_inv] at a₁ b₁ b₂ b₃ ⊢
      linear_combination (norm := abel) a₁ - b₁ - b₂ + b₃)
  refine ⟨g, (gtRel_iff gp hT hc hw u g₀ g).2 ⟨by rw [hgb, hb], fun χ y J J' hJ hJ' => ?_⟩⟩
  have v : vS (g.s (e χ)) y J' = vS (t (e.symm (e χ))) y J' := hg _ y J' hJ'
  rw [v, AddEquiv.symm_apply_apply, hgb]
  exact vt χ y J J' hJ hJ'
end GlobalTheory.ArcTransport
