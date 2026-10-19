-- Prove2me | solution 1 for MazurTransfer.ActualAffineSectionRingBasicOpenTransport.sectionsRingIso_coefficients_of_over
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T05:47:55.491078+00:00
-- url     : https://prove2.me/submissions/58e069bf-e088-4c6a-865e-91af0f97cbce

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact structural coefficient map under an actual affine-open section-ring comparison, for an isomorphism that lies over the specified base.
Named downstream consumers: both actual finite-chart R-algebra section comparisons in original order-thirteen FiniteMapData.
The argument adapts the original checked section-comparison proofs and retains all morphism identities. -/
import Mathlib
import Definitions.Def_MazurTransfer_ActualAffineSectionRingTransport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open MazurTransfer.ActualAffineSectionRingBasicOpenTransport

theorem solution (R : Type u) [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (B : Type u) [CommRing B] [Algebra R B]
    (e : Spec (.of B) ≅ U.toScheme)
    (he : e.hom ≫ U.ι ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    (Scheme.ΓSpecIso (.of R)).inv ≫
      c.appLE ⊤ U (by intro x hx; exact trivial) ≫ (sectionsRingIso U e).hom =
      CommRingCat.ofHom (algebraMap R B) := by
  have htop : c.appLE ⊤ U (by intro x hx; exact trivial) ≫ U.topIso.inv =
      (U.ι ≫ c).appTop :=
    c.appLE_map (by intro x hx; exact trivial) (eqToHom U.ι_image_top).op
  change (Scheme.ΓSpecIso (.of R)).inv ≫
    c.appLE ⊤ U (by intro x hx; exact trivial) ≫ U.topIso.inv ≫
      e.hom.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom = _
  have H := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
    e.hom.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom) htop
  calc
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ c).appTop ≫
        e.hom.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom := by
      simpa only [Category.assoc] using H
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop ≫
          (Scheme.ΓSpecIso (.of B)).hom := by
      have H2 := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
        (Scheme.ΓSpecIso (.of B)).hom) (congrArg Scheme.Hom.appTop he)
      simpa only [Scheme.Hom.comp_appTop, Category.assoc] using H2
    _ = _ := by simp

#print axioms solution
