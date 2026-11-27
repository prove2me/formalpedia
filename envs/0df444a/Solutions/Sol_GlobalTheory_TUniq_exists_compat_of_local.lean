-- Prove2me | solution 1 for GlobalTheory.TUniq.exists_compat_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:09.464589+00:00
-- url     : https://prove2.me/submissions/8ed929f6-0086-4f45-bde7-e9fc0cdfd08f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Theorems.Thm_GlobalTheory_TUniq_GeoGood_symm
import Theorems.Thm_GlobalTheory_TUniq_Compat_unique
import Theorems.Thm_GlobalTheory_TUniq_Compat_comp
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
namespace GlobalTheory.TUniq
theorem _root_.solution [IsReduced S] {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg)
    (H : ∀ p : t.A.left, ∃ (X : Scheme.{0}) (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left), IsOpenImmersion c₀ ∧
      p ∈ Set.range c₀ ∧ Compat t t' c₀ f) : ∃ φ, Compat t t' (𝟙 _) φ := by
  choose X c₀ f hc₀ hp hf using H
  have := t.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  let 𝒰 : t.A.left.OpenCover := Scheme.Cover.mkOfCovers _ X c₀ (fun p => ⟨p, hp p⟩) hc₀
  have hc : ∀ p q, pullback.fst (𝒰.f p) (𝒰.f q) ≫ f p = pullback.snd _ _ ≫ f q := fun p q => by
    have := hc₀ p
    have := hc₀ q
    have : IsReduced (pullback (c₀ p) (c₀ q)) := isReduced_of_isOpenImmersion (pullback.fst (c₀ p) (c₀ q) ≫ c₀ p)
    exact ((hf p).comp (pullback.fst (c₀ p) (c₀ q))).unique hd hg
      (by rw [pullback.condition]; exact (hf q).comp (pullback.snd (c₀ p) (c₀ q)))
  have e : ∀ p, c₀ p ≫ 𝒰.glueMorphisms f hc = f p := fun p => 𝒰.ι_glueMorphisms f hc p
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun p => ?_, fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y hy => ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (e p)).trans ((hf p).1.trans
      (congrArg _ (Category.id_comp _).symm)))
  · let p := y (default : PrimeSpectrum B)
    have := hc₀ p
    have hr : Set.range y ⊆ Set.range (c₀ p) := by
      rintro _ ⟨q, rfl⟩
      obtain rfl : q = (default : PrimeSpectrum B) := Subsingleton.elim (α := PrimeSpectrum B) _ _
      exact hp _
    have l := IsOpenImmersion.lift_fac (c₀ p) y hr
    rw [← l, Category.assoc, e]
    exact (hf p).2 K su u x ψ ψ' h₁ h₂ B z _ (l.trans ((Category.comp_id _).symm.trans hy))
end GlobalTheory.TUniq
