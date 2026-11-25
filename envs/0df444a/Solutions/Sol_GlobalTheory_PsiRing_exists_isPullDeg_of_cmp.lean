-- Prove2me | solution 1 for GlobalTheory.PsiRing.exists_isPullDeg_of_cmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:18.560428+00:00
-- url     : https://prove2.me/submissions/de9f2708-60c7-4098-9561-ae0be7b7188e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsPullDegOfComparison
import Theorems.Thm_GlobalTheory_PsiSpread_exists_psiOn
import Theorems.Thm_GlobalTheory_TauPull_jK_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory GlobalTheory.PsiRing
namespace GlobalTheory.PsiRing
theorem _root_.solution : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ W) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine ⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW,
    (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · exact (maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr
  · obtain ⟨b, -, vb⟩ := exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)
    have hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x) :=
      (Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))
    refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have e₁ := vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
      rw [pw, Fintype.prod_unique] at e₁
      refine (gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))
    · obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (D'.xK x y)
      obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
      have mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p := hp ▸ hJ _
      have e₁ := vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)
      have e₂ := hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)
      have w₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))
      rw [Category.assoc, Category.assoc, l₁, l₂, Category.comp_id] at w₁
      refine (val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans
        (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
      rw [Category.id_comp, Category.id_comp]
      exact (val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm
end GlobalTheory.PsiRing
