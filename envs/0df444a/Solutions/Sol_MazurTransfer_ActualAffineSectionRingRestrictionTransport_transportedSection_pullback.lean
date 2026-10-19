-- Prove2me | solution 1 for MazurTransfer.ActualAffineSectionRingRestrictionTransport.transportedSection_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:55:45.42414+00:00
-- url     : https://prove2.me/submissions/113f4af9-f1da-4c86-a1ea-d94576741190

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transported affine sections pull back to their literal
coordinate images along a Spec morphism landing in the affine open.
Named downstream consumer: reciprocal parameter product on the actual
order-13 two-chart intersection.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTransfer.ActualAffineSectionRingBasicOpenTransport
namespace AffineSectionRestrictionPublicProof20261017
variable {X : Scheme.{u}} (U : X.Opens) {B A : Type u} [CommRing B] [CommRing A] 
theorem inclusion_appLE_self_top :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE]
  rfl
theorem composite_appLE (k : Spec (.of A) ⟶ U.toScheme)
    (h : ⊤ ≤ (k ≫ U.ι) ⁻¹ᵁ U) :
    (k ≫ U.ι).appLE U ⊤ h = U.topIso.inv ≫ k.appTop := by
  have hc := Scheme.Hom.appLE_comp_appLE k U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (show ⊤ ≤ k ⁻¹ᵁ ⊤ by simp)
  rw [inclusion_appLE_self_top] at hc
  have ht : k.appLE ⊤ ⊤ (by simp) = k.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, Scheme.Hom.preimage_top,
      homOfLE_refl, op_id, Functor.map_id]
    exact Category.comp_id _
  rw [ht] at hc
  exact hc.symm
end AffineSectionRestrictionPublicProof20261017
open AffineSectionRestrictionPublicProof20261017
theorem solution {X : Scheme.{u}} (U : X.Opens) {B A : Type u} [CommRing B] [CommRing A]  (e : Spec (.of B) ≅ U.toScheme)
    (φ : B →+* A) (b : B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ⁻¹ᵁ U) :
    (Scheme.ΓSpecIso (.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι).appLE U ⊤ h
        (transportedSection U e b)) = φ b := by
  have hq := (sectionsRingIso U e).commRingCatIsoToRingEquiv.apply_symm_apply b
  change (Scheme.ΓSpecIso (.of B)).hom
    (e.hom.appTop (U.topIso.inv (transportedSection U e b))) = b at hq
  have hc := composite_appLE U (Spec.map (CommRingCat.ofHom φ) ≫ e.hom)
    (show ⊤ ≤ ((Spec.map (CommRingCat.ofHom φ) ≫ e.hom) ≫ U.ι) ⁻¹ᵁ U by
      simpa only [Category.assoc] using h)
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have hp := congrArg (fun k : Γ(Spec (.of B), ⊤) ⟶ CommRingCat.of A =>
    k (e.hom.appTop (U.topIso.inv (transportedSection U e b)))) hn
  have hd : (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι).appLE U ⊤ h =
      U.topIso.inv ≫ (Spec.map (CommRingCat.ofHom φ) ≫ e.hom).appTop := by
    simpa only [Category.assoc] using hc
  rw [hd, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (.of A)).hom
    ((Spec.map (CommRingCat.ofHom φ)).appTop
      (e.hom.appTop (U.topIso.inv (transportedSection U e b)))) = φ b
  exact hp.trans (congrArg φ hq)
#print axioms solution
