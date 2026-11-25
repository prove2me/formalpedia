-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.eq_mul_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:00:41.929133+00:00
-- url     : https://prove2.me/submissions/8ee2935e-b401-41bb-9f38-8e90f1345a8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_GlobalTheory_ZJ_AddExt_mul_left_comp
import Theorems.Thm_GlobalTheory_ZJ_AddExt_isDominant_gPt
import Theorems.Thm_GlobalTheory_ZJ_AddExt_isPullback_a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution (C : Core) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c d : Over.mk (spMap τ.j) ⟶ τ.H) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (hc : a₀ ≫ (fst C.A C.A).left ≫ C.a = gPt p ≫ c.left ≫ τ.f)
    (hd : a₀ ≫ (snd C.A C.A).left ≫ C.a = gPt p ≫ d.left ≫ τ.f)
    (b : Sp (OO p) ⟶ C.P.left) (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = y) :
    b = (c * d).left ≫ τ.f ≫ C.G.ι := by
  have := isDominant_gPt p
  have := C.proper
  have hA := isPullback_a C
  have : IsOpenImmersion C.a := MorphismProperty.of_isPullback hA.flip inferInstance
  have hinj : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  let k : Sp (PadicAlgCl p) ⟶ Sp (FractionRing τ.V) := spMap (IsFractionRing.lift hinj)
  have hk : k ≫ Out.jK τ.V = gPt p ≫ spMap τ.j := by
    simp only [k, ← Spec.map_comp]
    congr 1
    ext x
    simp
  refine ext_of_isDominant_of_isSeparated C.P.hom ?_ (gPt p) ?_
  · have h1 : τ.f ≫ C.G.ι ≫ C.P.hom = τ.H.hom ≫ τ.y₀ := τ.f_over
    have h2 : (c * d).left ≫ τ.H.hom = spMap τ.j := Over.w _
    rw [hb', Category.assoc, Category.assoc, h1, reassoc_of% h2, τ.fac]
  have wc : c.left ≫ τ.H.hom = spMap τ.j := Over.w _
  have wd : d.left ≫ τ.H.hom = spMap τ.j := Over.w _
  let c' : Over.mk k ⟶ (Over.pullback (Out.jK τ.V)).obj τ.H :=
    Over.homMk (pullback.lift (gPt p ≫ c.left) k (by rw [hk, Category.assoc, wc])) (pullback.lift_snd _ _ _)
  let d' : Over.mk k ⟶ (Over.pullback (Out.jK τ.V)).obj τ.H :=
    Over.homMk (pullback.lift (gPt p ≫ d.left) k (by rw [hk, Category.assoc, wd])) (pullback.lift_snd _ _ _)
  have hc' : c'.left ≫ pullback.fst τ.H.hom (Out.jK τ.V) = gPt p ≫ c.left := pullback.lift_fst _ _ _
  have hd' : d'.left ≫ pullback.fst τ.H.hom (Out.jK τ.V) = gPt p ≫ d.left := pullback.lift_fst _ _ _
  let c₁ : Over.mk (k ≫ Out.jK τ.V) ⟶ τ.H := Over.homMk (gPt p ≫ c.left) (by simp [hk, wc])
  let d₁ : Over.mk (k ≫ Out.jK τ.V) ⟶ τ.H := Over.homMk (gPt p ≫ d.left) (by simp [hk, wd])
  have e₁ : (c₁ * d₁).left = (c' * d').left ≫ pullback.fst τ.H.hom (Out.jK τ.V) :=
    (isGrpPullback_pullback τ.H (Out.jK τ.V)).2 (Over.mk k) c' d' c₁ d₁ hc'.symm hd'.symm
  have e₂ : (c₁ * d₁).left = gPt p ≫ (c * d).left := mul_left_comp (gPt p) hk.symm c d c₁ d₁ rfl rfl
  have wφ : τ.φ ≫ C.A.hom = pullback.snd τ.H.hom (Out.jK τ.V) ≫ τ.yK := τ.φ_cart.1.w
  have wc' : c'.left ≫ pullback.snd τ.H.hom (Out.jK τ.V) = k := pullback.lift_snd _ _ _
  have wd' : d'.left ≫ pullback.snd τ.H.hom (Out.jK τ.V) = k := pullback.lift_snd _ _ _
  let c₂ : Over.mk (k ≫ τ.yK) ⟶ C.A := Over.homMk (c'.left ≫ τ.φ)
    (by change (c'.left ≫ τ.φ) ≫ C.A.hom = k ≫ τ.yK; rw [Category.assoc, wφ, reassoc_of% wc'])
  let d₂ : Over.mk (k ≫ τ.yK) ⟶ C.A := Over.homMk (d'.left ≫ τ.φ)
    (by change (d'.left ≫ τ.φ) ≫ C.A.hom = k ≫ τ.yK; rw [Category.assoc, wφ, reassoc_of% wd'])
  have e₃ : (c₂ * d₂).left = (c' * d').left ≫ τ.φ := τ.φ_cart.2 (Over.mk k) c' d' c₂ d₂ rfl rfl
  have e₄ : (lift c₂ d₂).left = a₀ := by
    apply pullback.hom_ext
    · have h1 : (lift c₂ d₂).left ≫ (fst C.A C.A).left = c'.left ≫ τ.φ := by
        rw [← Over.comp_left, lift_fst]; rfl
      change _ ≫ (fst C.A C.A).left = _ ≫ (fst C.A C.A).left
      rw [h1, ← cancel_mono C.a, Category.assoc, Category.assoc, hc, τ.φ_f, reassoc_of% hc']
    · have h1 : (lift c₂ d₂).left ≫ (snd C.A C.A).left = d'.left ≫ τ.φ := by
        rw [← Over.comp_left, lift_snd]; rfl
      change _ ≫ (snd C.A C.A).left = _ ≫ (snd C.A C.A).left
      rw [h1, ← cancel_mono C.a, Category.assoc, Category.assoc, hd, τ.φ_f, reassoc_of% hd']
  have e₅ : a₀ ≫ (μ[C.A]).left = (c' * d').left ≫ τ.φ := by
    rw [← e₃, ← e₄, ← Over.comp_left]; rfl
  rw [hb, reassoc_of% e₅, reassoc_of% τ.φ_f, ← reassoc_of% e₂, e₁, Category.assoc]
end GlobalTheory.ZJ.AddExt
