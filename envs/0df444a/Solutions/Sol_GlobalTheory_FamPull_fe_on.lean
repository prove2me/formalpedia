-- Prove2me | solution 1 for GlobalTheory.FamPull.fe_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:03.876742+00:00
-- url     : https://prove2.me/submissions/c3b29aea-a3c8-43da-8c77-dc2d9092e594

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_GlobalTheory_FamPull_sval_eq_of_app_injective
import Theorems.Thm_GlobalTheory_FamPull_famFE_iff
import Theorems.Thm_GlobalTheory_FamPull_exists_feGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
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
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
namespace GlobalTheory.FamPull
theorem _root_.solution (hG : GlobalFnsSt) (ψW : PsiOn D W) {k : ℕ} (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α)
    (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1) (mu α : D.X)
    {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W) (x : T ⟶ D.P.A) {z : T.left} {J} (hJ : Good D.P.L z J) :
    sval (f (α + k • mu)) x.left z J = sval (f α) (x * cP D T mu).left z J *
      (feUnit D k mu α x z J (fun χ => val (ψW.psi χ) κ.left z J) (val (D.rigW W) κ.left z J)).val := by
  obtain ⟨K, _, φ, ε, u, hu, hF, hv⟩ := exists_feGen ψW k mu α
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ TW W ⊗ D.P.A) (z : T.left) (J), Good D.P.L z J →
      sval (pullSec D.P.L _ _ (f (α + k • mu)) (snd (TW W) D.P.A).left) ρ.left z J =
        sval (f (α + k • mu)) (ρ ≫ snd _ _).left z J ∧
      sval (pullMulSec (f α) (snd (TW W) D.P.A * cP D _ mu).left u hu) ρ.left z J =
        sval (f α) ((ρ ≫ snd _ _) * cP D T mu).left z J *
          (feUnit D k mu α (ρ ≫ snd _ _) z J (fun χ => val (ψW.psi χ) (ρ ≫ fst _ _).left z J)
            (val (D.rigW W) (ρ ≫ fst _ _).left z J)).val := fun T ρ z J hJ =>
    ⟨sval_pullSec _ _ _ _ _ z hJ, by
      rw [sval_pullMulSec _ _ _ _ _ z hJ, hv T ρ z J hJ, ← Over.comp_left, MonObj.comp_mul, comp_cP]⟩
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  let π : (TW W ⊗ D.P.A).left ⟶ W.toScheme := (fst (TW W) D.P.A).left
  have : Flat π := by
    have := D.P.isAb.smooth
    show Flat (pullback.fst _ _)
    infer_instance
  let T₀ : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.snd (jK R ∣_ W) π ≫ (TW W ⊗ D.P.A).hom)
  let h : T₀ ⟶ TW W ⊗ D.P.A := Over.homMk (pullback.snd (jK R ∣_ W) π) rfl
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  have hc : (pullback.fst (jK R ∣_ W) π ≫ (jK R ⁻¹ᵁ W).ι) ≫ jK R = T₀.hom := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc]
    exact congrArg (pullback.snd (jK R ∣_ W) π ≫ ·) (Over.w (fst (TW W) D.P.A))
  let σ : T₀ ⟶ TF (R := R) (FractionRing R) := Over.homMk (pullback.fst (jK R ∣_ W) π ≫ (jK R ⁻¹ᵁ W).ι) (by
    show _ ≫ jFK (R := R) (FractionRing R) ≫ jK R = _
    rw [hj, Category.id_comp]; exact hc)
  have hinj : ∀ U : (TW W ⊗ D.P.A).left.Opens, Function.Injective (h.left.app U).hom := fun U =>
    (pullback.snd (jK R ∣_ W) π).app_injective U
  have H : ∀ (y : T₀.left) I, Good D.P.L y I →
      sval (pullSec D.P.L _ _ (f (α + k • mu)) (snd (TW W) D.P.A).left) h.left y I =
        sval (pullMulSec (f α) (snd (TW W) D.P.A * cP D _ mu).left u hu) h.left y I := fun y I hI => by
      obtain ⟨k₁, k₂⟩ := key T₀ h y I hI
      have e := (famFE_iff hG F.s f hs).1 F.fe mu α T₀ (lift σ (h ≫ snd _ _)) y I hI
      have hσ : σ.left ≫ jFK (R := R) (FractionRing R) = pullback.fst (jK R ∣_ W) π ≫ (jK R ⁻¹ᵁ W).ι :=
        (congrArg (σ.left ≫ ·) hj).trans (Category.comp_id _)
      rw [lift_snd, lift_fst] at e
      have b : (h ≫ fst _ _).left = pullback.fst (jK R ∣_ W) π ≫ jK R ∣_ W := pullback.condition.symm
      have vψ : ∀ χ, val (ψW.psi χ) (h ≫ fst _ _).left y I =
          val (D.psi χ) (σ.left ≫ jFK (R := R) (FractionRing R)) y I := fun χ => by
        rw [b, hσ]
        exact (val_pull hI _ _ _).symm.trans ((val_corr hI (ψW.psi_eq χ) _).trans (val_pull hI _ _ _))
      have vρ : val (D.rigW W) (h ≫ fst _ _).left y I =
          val D.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) y I :=
        (val_pull hI _ _ _).trans (Eq.trans (congrArg (fun q => val D.rig q y I)
          ((Over.w (h ≫ fst _ _)).trans (hc.symm.trans (congrArg (· ≫ jK R) hσ.symm)))) (val_pull hI _ _ _).symm)
      rw [k₁, k₂, e, vρ, funext vψ]
  have E := sval_eq_of_app_injective D.P.isLB hF h.left hinj H T.left (lift κ x).left z J hJ
  obtain ⟨k₁, k₂⟩ := key T (lift κ x) z J hJ
  rw [lift_snd] at k₁
  rw [lift_fst, lift_snd] at k₂
  exact k₁.symm.trans (E.trans k₂)
end GlobalTheory.FamPull
