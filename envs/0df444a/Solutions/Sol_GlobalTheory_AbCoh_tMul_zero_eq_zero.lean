-- Prove2me | solution 1 for GlobalTheory.AbCoh.tMul_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:25:40.946261+00:00
-- url     : https://prove2.me/submissions/903d58dd-6d82-4e32-a342-d84b5f5826a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocyclePullbackIffPreimageAffineHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmallExtensionElementMulZeroClassEqZero
import Theorems.Thm_GlobalTheory_AbCoh_red_iff_pre
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_AbCoh_pre__surjective_and_ker_5a1e5300be4a
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF y hy
  have iφ : IsClosedImmersion φ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hE.1)
  have iφ₀ : IsClosedImmersion φ₀ :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
      (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hE.2.2.1)
  obtain ⟨f, c, hc, rfl, hred⟩ := hy
  obtain ⟨c₀, hc₀, hcl⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).1 f 0).1 hred
  rw [map_zero, CatCoh.H1.mk_eq_zero] at hcl
  obtain ⟨g₀, hg₀⟩ := hcl
  have hS := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hE hF
  choose g hg using fun U => (hS U).2.2.1 (g₀ U)
  have key : ∀ U V (a : U ⟶ V), t • (f U V a - d0 (OAff s) g U V a) = 0 := by
    intro U V a
    rw [← (hS V).2.2.2]
    have hn := (preCoef h₀.w).naturality a (g U)
    have e := congrFun (congrFun (congrFun hg₀ U) V) a
    change preα φ₀ s s₀ V (mp (OAff s) a (g U)) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U (g U)) at hn
    rw [amitsur_d0_apply, hc₀] at e
    rw [amitsur_d0_apply, map_sub, map_sub, hn, hg, hg, ← e]
    ring
  refine CatCoh.H1.mk_eq_zero.2 ⟨t • g, ?_⟩
  rw [hc, map_smul]
  funext U V a
  have := key U V a
  simp only [Pi.smul_apply]
  rw [smul_sub, sub_eq_zero] at this
  exact this.symm
end GlobalTheory.AbCoh
