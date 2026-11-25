-- Prove2me | solution 1 for GlobalTheory.psiIn_of_isPullDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:02.790002+00:00
-- url     : https://prove2.me/submissions/b15a5584-ec3b-43a3-85c3-3c949bcfb5f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Theorems.Thm_GlobalTheory_PsiInPull_jK_mem
import Theorems.Thm_GlobalTheory_PsiInPull_res_toOpen
import Theorems.Thm_GlobalTheory_PsiInPull_app_toOpen
import Theorems.Thm_GlobalTheory_PsiInPull_exists_of_locally
import Theorems.Thm_GlobalTheory_PsiInPull_mem_wchart
import Theorems.Thm_GlobalTheory_PsiInPull_psiOn_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
noncomputable section
open GlobalTheory
open PsiInPull
namespace GlobalTheory
theorem _root_.solution (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R')
    (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (x : D'.X) (J : Ideal R) (J' : Ideal R')
    (hJ : J.map φ ≤ J') (H : D.PsiIn (hD.xe x) J) : D'.PsiIn x J' := by
  intro j' V' hV' hle' h'
  obtain ⟨q, rfl⟩ : ∃ q, j' = fun _ => q := ⟨j' PUnit.unit, rfl⟩
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R'))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R')))
  by_cases hne : ∃ z, jK R' z ∈ V'
  swap
  · exact ⟨0, Ideal.zero_mem _, fn_ext fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨z, hz⟩ := hne
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) with hΦ
  have hcp : (D'.c x).left ≫ Φ = specOf φ ≫ (D.c (hD.xe x)).left := hD.c_pr x
  have hxK : D'.xK x = jK R' ≫ (D'.c x).left := rfl
  have cW : hD.g ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ Φ := by
    rw [hxK, Category.assoc, hcp, ← Category.assoc (jK R'), ← hD.g_comm, Category.assoc]; rfl
  obtain ⟨r', hr', e'⟩ := exists_of_locally J' z
    (gm (𝟙 _) z (LB.wchart D'.P.L (fun _ : PUnit => D'.xK x) (fun _ => q)) ((D'.psi x).s (fun _ => q))).val
    V' hV' hz (by
    intro v hv
    obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c (hD.xe x)).left (specOf φ v))
    obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show specOf φ v ∈ ((D.c (hD.xe x)).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
      ((D.c (hD.xe x)).left ⁻¹ᵁ D.P.L.U p).isOpen
    have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK (hD.xe x)) (fun _ => -1)).U (fun _ => p) :=
      fun y hy => mem_wchart _ _ _ _ (hVp hy)
    obtain ⟨r, hrJ, hr⟩ := H (fun _ => p) V hV hVp h
    have hzU : jK R' z ∈ V' ⊓ specOf φ ⁻¹ᵁ V := jK_mem z _ (fun h0 =>
      (h0.le (show v ∈ V' ⊓ specOf φ ⁻¹ᵁ V from ⟨hv, hvV⟩) : v ∈ (⊥ : (Spec (CommRingCat.of R')).Opens)))
    have hU : V' ⊓ specOf φ ⁻¹ᵁ V ≤ (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) := fun y hy =>
      ⟨mem_pull.2 ((congrArg (fun m => m y ∈ D.P.L.U p) hcp).mpr (hVp hy.2)), hle' hy.1⟩
    have m₁ : (𝟙 (TK R').left : (TK R').left ⟶ (TK R').left) z ∈
        D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) := hU hzU
    have mp : Φ (D'.xK x z) ∈ D.P.L.U p := mem_pull.1 m₁.1
    have mW : (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left (hD.g z) ∈ D.P.L.U p :=
      (congrArg (fun m => m z ∈ D.P.L.U p) cW).mpr mp
    have e₁ := congrArg (gm (𝟙 (TK R').left) z (D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q)))
      (hb (fun _ => p) q)
    have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
        ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _))) (gm_res _ z _ m₁ _))))
    have e₂ := (gm_corr D.P.L hcorr (𝟙 (TK R').left) z p (mem_wchart _ _ _ _ mp) (mem_wchart _ _ _ _ mW)).trans
      (gm_pullGen D.P.L _ _ _ hD.g (𝟙 (TK R').left) z _ (mem_wchart _ _ _ _ mW))
    have hgz : hD.W.ι (hD.g z) ∈ V := (congrArg (fun m => m z ∈ V) hD.g_comm).mpr hzU.2
    have e₃ := psiOn_val hD.psiW (hD.xe x) p V hVp h r hr hD.g z hgz
    have e₄ := e₂.symm.trans e₁'
    rw [Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at e₄
    erw [Category.id_comp] at e₄
    refine ⟨V' ⊓ specOf φ ⁻¹ᵁ V, inf_le_left, ⟨hv, hvV⟩,
      ((Spec (CommRingCat.of R')).presheaf.map (homOfLE hU).op).hom
        (((D'.c x).left.app _).hom (hD.w.s (fun _ => p, q)).val) *
      ((Spec (CommRingCat.of R')).presheaf.map (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom
        (((specOf φ).app V).hom r), Ideal.mul_mem_left _ _ ?_, ?_⟩
    · have h1 := Ideal.mem_map_of_mem (((Spec (CommRingCat.of R')).presheaf.map
        (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom.comp ((specOf φ).app V).hom) hrJ
      rw [Ideal.map_map] at h1
      refine Ideal.map_mono (f := DegPre.toOpen (V' ⊓ specOf φ ⁻¹ᵁ V)) hJ ?_
      rw [Ideal.map_map]
      have e5 : (DegPre.toOpen (V' ⊓ specOf φ ⁻¹ᵁ V)).comp φ = (((Spec (CommRingCat.of R')).presheaf.map
          (homOfLE (inf_le_right : V' ⊓ specOf φ ⁻¹ᵁ V ≤ _)).op).hom.comp ((specOf φ).app V).hom).comp
          (DegPre.toOpen V) :=
        RingHom.ext fun a => ((congrArg _ (app_toOpen φ V a)).trans (res_toOpen inf_le_right _)).symm
      rw [e5]
      exact h1
    · refine Eq.trans ?_ (congrArg Units.val e₄)
      refine (gs_mul _ _ _ hzU _ _).trans (congrArg₂ (· * ·) ?_ ?_)
      · exact (gs_res _ _ hU hzU _).trans ((gs_pull (jK R') (D'.c x).left z _ m₁ _).trans (gs_unit (D'.xK x) z ((D.P.L.pull Φ).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _))
      · refine (gs_res _ _ _ hzU _).trans ((gs_pull (jK R') (specOf φ) z V hzU.2 r).trans ?_)
        exact (congrArg (fun m => gs m z V r) hD.g_comm).symm.trans e₃.symm)
  refine ⟨r', hr', fn_ext fun y hy => ?_⟩
  obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R'))) y z
  exact (gs_pull (𝟙 _) (jK R') y V' hz r').trans (e'.trans
    ((gs_res (𝟙 _) y h' hy _).trans (gs_unit _ _ _ (h' hy) _)).symm)
end GlobalTheory
