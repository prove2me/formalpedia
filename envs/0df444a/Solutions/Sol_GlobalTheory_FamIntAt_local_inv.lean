-- Prove2me | solution 1 for GlobalTheory.FamIntAt.local_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:27:16.299348+00:00
-- url     : https://prove2.me/submissions/ba6c032a-aea4-4bfb-aa53-7987cba93470

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Theorems.Thm_GlobalTheory_FamIntAt_eq_genPt
import Theorems.Thm_GlobalTheory_PsiInPull_jK_mem
import Theorems.Thm_GlobalTheory_PsiInPull_mem_wchart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FamIntAt
theorem _root_.solution {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψ : PsiOn D W) (ρ : D.X)
    (g : Γ(Spec (CommRingCat.of R), ⊤)) (hgW : (Spec (CommRingCat.of R)).basicOpen g ≤ W)
    (hg : jK R (genPt R) ∈ (Spec (CommRingCat.of R)).basicOpen g) (q : Spec (CommRingCat.of R)) :
    ∃ (j : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens) (n : ℕ) (a : Γ(Spec (CommRingCat.of R), V)), q ∈ V ∧
      V ≤ (D.c ρ).left ⁻¹ᵁ D.P.L.U j ∧ gs (jK R) (genPt R) V a = gs (jK R) (genPt R) ⊤ g ^ n *
        ((gm (𝟙 _) (genPt R) (LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => j))
          ((D.psi ρ).s (fun _ => j)))⁻¹).val := by
  obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c ρ).left q)
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
    (show q ∈ ((D.c ρ).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
    ((D.c ρ).left ⁻¹ᵁ D.P.L.U p).isOpen
  have hm : jK R (genPt R) ∈ V := PsiInPull.jK_mem _ V fun h0 => (h0.le hvV : q ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
  set V' := (Spec (CommRingCat.of R)).basicOpen (resTop V g) with hV'
  have eV : V' = V ⊓ (Spec (CommRingCat.of R)).basicOpen g := Scheme.basicOpen_res _ _ _
  have hW : V' ≤ W := eV.le.trans (inf_le_right.trans hgW)
  have hVV : V' ≤ V := eV.le.trans inf_le_left
  have hm' : jK R (genPt R) ∈ V' := eV.ge ⟨hm, hg⟩
  have hle : W.ι ⁻¹ᵁ V' ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c ρ).left) (fun _ => p) :=
    fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp (hVV hy))
  have : IsIso (W.ι.app V') := Scheme.Hom.isIso_app W.ι V' (by rw [Scheme.Opens.opensRange_ι]; exact hW)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (W.ι.app V')).2
    ((W.toScheme.presheaf.map (homOfLE hle).op).hom (((ψ.psi ρ).s (fun _ => p))⁻¹).val)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen _ V hV (resTop V g) x
  refine ⟨p, V, n, y, hvV, hVp, ?_⟩
  have hW0 : jK R (genPt R) ∈ W := hW hm'
  let lf : Spec (CommRingCat.of (FractionRing R)) ⟶ (jK R ⁻¹ᵁ W).toScheme :=
    IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) (by
      rintro _ ⟨z, rfl⟩
      obtain rfl := eq_genPt z
      exact ⟨⟨_, hW0⟩, rfl⟩)
  have hlf : lf ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  have hι : (lf ≫ (jK R ∣_ W)) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hlf, Category.id_comp]
  have hpt : (lf ≫ (jK R ∣_ W)) (genPt R) ∈ W.ι ⁻¹ᵁ V' := (congrArg (fun m => m (genPt R) ∈ V') hι).mpr hm'
  obtain ⟨J, hJ, hJp⟩ := exists_good D.P.L D.P.isLB (genPt R) (fun _ : PUnit => D.xK ρ) (fun _ => p)
    (fun _ _ _ => rfl) (fun _ => hVp hm)
  have e₀ := val_corr hJ (ψ.psi_eq ρ) lf
  rw [val_pull hJ, val_pull hJ, hlf, val_of _ _ _ J (fun _ => p) (fun _ => by
      refine Eq.trans (congrArg J ?_) (hJp PUnit.unit)
      show (lf ≫ (jK R ∣_ W)) ≫ W.ι ≫ (D.c ρ).left = jK R ≫ (D.c ρ).left
      rw [← Category.assoc, hι]),
    val_of _ _ _ J (fun _ => p) (fun _ => by rw [Category.id_comp]; exact hJp PUnit.unit)] at e₀
  have e₁ : gs (jK R) (genPt R) V' x = ((gm (𝟙 _) (genPt R) (LB.wchart D.P.L (fun _ : PUnit => D.xK ρ) (fun _ => p))
      ((D.psi ρ).s (fun _ => p)))⁻¹).val := by
    rw [← e₀]
    refine (congrArg (fun m => gs m (genPt R) V' x) hι).symm.trans ((gs_pull _ W.ι _ V' hpt x).symm.trans ?_)
    refine (congrArg (gs (lf ≫ (jK R ∣_ W)) (genPt R) (W.ι ⁻¹ᵁ V')) hx).trans ?_
    exact (gs_res _ _ hle hpt _).trans ((gs_unit _ _ _ (hle hpt) _).trans (congrArg Units.val (map_inv _ _)))
  have e₂ := congrArg (gs (jK R) (genPt R) V') hy
  refine (gs_res _ _ hVV hm' y).symm.trans (e₂.trans ((gs_mul _ _ _ hm' _ _).trans (congrArg₂ (· * ·) ?_ e₁)))
  rw [gs_eq _ _ _ hm', map_pow, map_pow, ← gs_eq _ _ _ hm']
  exact congrArg (· ^ n) ((gs_res _ _ hVV hm' _).trans (gs_res _ _ le_top hm _))
end GlobalTheory.FamIntAt
