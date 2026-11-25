-- Prove2me | solution 1 for GlobalTheory.TauBalPull.tauW_bal_corr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:33:58.090235+00:00
-- url     : https://prove2.me/submissions/d9ba1b38-36ea-4782-b67a-bc3657f2ac1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauPull_corr_of_dense
import Theorems.Thm_GlobalTheory_TauPull_jK_mem
import Theorems.Thm_GlobalTheory_TauPull_val_tau
import Theorems.Thm_GlobalTheory_TauPull_val_tauW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
namespace GlobalTheory.TauBalPull
theorem _root_.solution (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    {K : Type} [Fintype K] {φ : K → ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) (a b a' b' y y' : D.X)
    (h : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (LB.pullGen D.P.L _ _ u (D.pt2 y y'))) (D.tau a' b')) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b)
        (LB.pullGen D.P.L _ _ u (lift (cP D (TW W) y) (cP D (TW W) y')).left)) (ψW.tau a' b') := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ h (𝟙 _))
    refine (val_mul hJ _ _ _).trans ?_
    rw [vτ, vτ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
    rw [Category.id_comp, ← Over.comp_left, comp_lift, comp_cP, comp_cP]
    rfl
end GlobalTheory.TauBalPull
