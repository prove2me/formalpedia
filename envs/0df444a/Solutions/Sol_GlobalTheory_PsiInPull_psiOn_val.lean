-- Prove2me | solution 1 for GlobalTheory.PsiInPull.psiOn_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:07.59128+00:00
-- url     : https://prove2.me/submissions/adda4944-a107-4677-bf70-e46be62a6ca7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Theorems.Thm_GlobalTheory_PsiInPull_gs_injective
import Theorems.Thm_GlobalTheory_PsiInPull_jK_mem
import Theorems.Thm_GlobalTheory_PsiInPull_mem_wchart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pullGen


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
open GlobalTheory.PsiInPull
namespace GlobalTheory.PsiInPull
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
    (ψ : PsiOn D W) (χ : D.X) (p : D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens)
    (hVp : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U p)
    (h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => p))
    (r : Γ(Spec (CommRingCat.of R), V))
    (hr : ((jK R).app V).hom r = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s (fun _ => p)).val)
    {Z : Scheme.{0}} (g : Z ⟶ W.toScheme) (z : Z) (hz : W.ι (g z) ∈ V) :
    (gm g z (LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p))
      ((ψ.psi χ).s (fun _ => p))).val = gs (g ≫ W.ι) z V r := by
  have hc : (toUnit (TW W) ≫ D.c χ).left = W.ι ≫ (D.c χ).left := rfl
  have hle : W.ι ⁻¹ᵁ V ≤ LB.wchart D.P.L (fun _ : PUnit => (toUnit (TW W) ≫ D.c χ).left) (fun _ => p) :=
    fun y hy => mem_wchart _ _ _ _ (hVp hy)
  obtain ⟨z₀⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have hW : jK R z₀ ∈ W := jK_mem z₀ W (fun h0 => by
    have : (g z).1 ∈ W := (g z).2
    exact (h0.le this : (g z).1 ∈ (⊥ : (Spec (CommRingCat.of R)).Opens)))
  have hV : jK R z₀ ∈ V := jK_mem z₀ V (fun h0 => by rw [h0] at hz; exact hz)
  let z₁ : (jK R ⁻¹ᵁ W).toScheme := ⟨z₀, hW⟩
  have hι : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hpt : W.ι ((jK R ∣_ W) z₁) = jK R z₀ := congrArg (fun q => q z₁) hι
  have hm : (jK R ∣_ W) z₁ ∈ W.ι ⁻¹ᵁ V := by
    show W.ι ((jK R ∣_ W) z₁) ∈ V
    rw [hpt]; exact hV
  have hdense : ∀ U : W.toScheme.Opens, U ≠ ⊥ → (jK R ∣_ W) z₁ ∈ U := by
    intro U hU
    have h1 : jK R z₀ ∈ W.ι ''ᵁ U := jK_mem z₀ _ (fun h0 => hU (by
      rw [← W.ι.preimage_image_eq U, h0]; rfl))
    rw [← hpt] at h1
    rw [← W.ι.preimage_image_eq U]; exact h1
  have n₂ : (jK R ⁻¹ᵁ W).ι z₁ ∈ jK R ⁻¹ᵁ V := hV
  have e₃ := (gm_pullGen D.P.L _ _ (ψ.psi χ) (jK R ∣_ W) (𝟙 _) z₁ (fun _ => p) (mem_wchart _ _ _ _ (hVp hm))).symm.trans
    ((gm_corr D.P.L (ψ.psi_eq χ) (𝟙 _) z₁ p (mem_wchart _ _ _ _ (hVp hm)) (mem_wchart _ _ _ _ (hVp hV))).trans
      (gm_pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι (𝟙 _) z₁ (fun _ => p) (mem_wchart _ _ _ _ (hVp hV))))
  rw [Category.id_comp, Category.id_comp] at e₃
  have e : (W.toScheme.presheaf.map (homOfLE hle).op).hom ((ψ.psi χ).s (fun _ => p)).val = (W.ι.app V).hom r := by
    refine gs_injective (jK R ∣_ W) z₁ hdense (W.ι ⁻¹ᵁ V) hm ?_
    refine ((gs_res _ _ hle hm _).trans ((gs_unit _ _ _ (hle hm) _).trans (congrArg Units.val e₃))).trans ?_
    refine Eq.trans ?_ (gs_pull (jK R ∣_ W) W.ι z₁ V hm r).symm
    rw [hι]
    refine Eq.trans ?_ (gs_pull (jK R ⁻¹ᵁ W).ι (jK R) z₁ V n₂ r)
    rw [hr]
    exact ((gs_res _ _ h n₂ _).trans (gs_unit _ _ _ (h n₂) _)).symm
  exact (gs_unit g z _ (hle hz) _).symm.trans ((gs_res g z hle hz _).symm.trans
    ((congrArg (gs g z (W.ι ⁻¹ᵁ V)) e).trans (gs_pull g W.ι z V hz r)))
end GlobalTheory.PsiInPull
