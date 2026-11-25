-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.bijective_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:01.291948+00:00
-- url     : https://prove2.me/submissions/0144f92e-6f50-4848-b7b7-0aba78d90541

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_tensPt_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_Axis_tensPt_snd
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Glue_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Sep_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van1_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van2_mono
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
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
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Sp R) (g : Y ⟶ Sp R)
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (U : X.affineOpens) (V : Y.affineOpens) (W : (pullback f g).affineOpens)
    (hW : W.1 = pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1) (s' : pullback f g ⟶ Sp R)
    (hU : W.1 ≤ pullback.fst f g ⁻¹ᵁ U.1) (hV : W.1 ≤ pullback.snd f g ⁻¹ᵁ V.1)
    (α : Sec f U.1 ⊗[R] Sec g V.1 →+* Sec s' W.1)
    (hα : ∀ b c, α (b ⊗ₜ c) = secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩ b *
      secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩ c) : Function.Bijective α := by
  haveI : Mono (affPt f U) := IsOpenImmersion.mono _
  haveI : Mono (affPt g V) := IsOpenImmersion.mono _
  have hr : Set.range (affPt s' W) = Set.range (tensPt f g U V) := by
    rw [range_tensPt]
    refine (W.2.range_fromSpec).trans ?_
    rw [hW]; rfl
  let e := IsOpenImmersion.isoOfRangeEq (affPt s' W) (tensPt f g U V) hr
  have he : e.hom ≫ tensPt f g U V = affPt s' W := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let a : CommRingCat.of (Sec f U.1 ⊗[R] Sec g V.1) ⟶ CommRingCat.of (Sec s' W.1) := Spec.preimage e.hom
  have ha : spMap a.hom = e.hom := Spec.map_preimage e.hom
  have hL : a.hom.comp Algebra.TensorProduct.includeLeftRingHom = secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩ := by
    have k : spMap (a.hom.comp Algebra.TensorProduct.includeLeftRingHom) ≫ affPt f U =
        spMap (secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩) ≫ affPt f U := by
      rw [secPull_affPt (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩, spMap_comp, Category.assoc, ha, ← tensPt_fst, ← Category.assoc, he]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (affPt f U)).1 k))
  have hR : a.hom.comp ((Algebra.TensorProduct.includeRight : Sec g V.1 →ₐ[R] Sec f U.1 ⊗[R] Sec g V.1) : Sec g V.1 →+* _) =
      secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩ := by
    have k : spMap (a.hom.comp ((Algebra.TensorProduct.includeRight : Sec g V.1 →ₐ[R] Sec f U.1 ⊗[R] Sec g V.1) : Sec g V.1 →+* _)) ≫ affPt g V =
        spMap (secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩) ≫ affPt g V := by
      rw [secPull_affPt (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩, spMap_comp, Category.assoc, ha, ← tensPt_snd, ← Category.assoc, he]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono (affPt g V)).1 k))
  have hEq : ∀ t, α t = a.hom t := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b c =>
      rw [hα, ← hL, ← hR, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      congr 1
      simp
  have hI : IsIso (Spec.map a) := by rw [Spec.map_preimage]; infer_instance
  have hb : Function.Bijective a.hom := isIso_SpecMap_iff.1 hI
  exact (funext hEq : ⇑α = ⇑a.hom) ▸ hb
end GlobalTheory.CompanionTheory.Axis
