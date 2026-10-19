-- Prove2me | solution 1 for MazurTransfer.ActualAffineSectionRingBasicOpenTransport.basicOpen_transport
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:55:31.682998+00:00
-- url     : https://prove2.me/submissions/120200ba-949d-47e9-8b93-01971a5903cd

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: basic opens transport through an actual Spec-to-open
isomorphism and its exact global section-ring comparison.
Named downstream consumers: the two actual single-section parameters in
order-13 FiniteMapData. No parameter or curve-specific identity is assumed.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTransfer.ActualAffineSectionRingBasicOpenTransport
theorem solution {X : Scheme.{u}} (U : X.Opens) {B : Type u} [CommRing B]  (e : Spec (.of B) ≅ U.toScheme) (b : B) :
    X.basicOpen (transportedSection U e b) =
      (e.hom ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen b := by
  have hq := (sectionsRingIso U e).commRingCatIsoToRingEquiv.apply_symm_apply b
  change (Scheme.ΓSpecIso (.of B)).hom
    (e.hom.appTop (U.topIso.inv (transportedSection U e b))) = b at hq
  have ht : e.hom.appTop (U.topIso.inv (transportedSection U e b)) =
      (Scheme.ΓSpecIso (.of B)).inv b := by
    have hh := congrArg (fun x : B => (Scheme.ΓSpecIso (.of B)).inv x) hq
    have hc : (Scheme.ΓSpecIso (.of B)).inv
        ((Scheme.ΓSpecIso (.of B)).hom
          (e.hom.appTop (U.topIso.inv (transportedSection U e b)))) =
        e.hom.appTop (U.topIso.inv (transportedSection U e b)) := by
      change ((Scheme.ΓSpecIso (.of B)).hom ≫ (Scheme.ΓSpecIso (.of B)).inv)
        (e.hom.appTop (U.topIso.inv (transportedSection U e b))) = _
      rw [Iso.hom_inv_id]
      rfl
    exact hc.symm.trans hh
  have hp : e.hom ⁻¹ᵁ U.toScheme.basicOpen (U.topIso.inv (transportedSection U e b)) =
      PrimeSpectrum.basicOpen b := by
    rw [Scheme.preimage_basicOpen_top, ht, basicOpen_eq_of_affine]
  have hi : e.hom ''ᵁ PrimeSpectrum.basicOpen b =
      U.toScheme.basicOpen (U.topIso.inv (transportedSection U e b)) := by
    rw [← hp, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, ← hi]
  apply SetLike.ext'
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e.hom z, ⟨z, hz, rfl⟩, rfl⟩
#print axioms solution
