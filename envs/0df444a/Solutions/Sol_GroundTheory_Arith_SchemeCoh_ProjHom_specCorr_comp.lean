-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:08.695905+00:00
-- url     : https://prove2.me/submissions/f138fd5e-4889-4ebc-8b9d-f9668aca0cb4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjHom
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh.ProjHom
theorem _root_.solution {Y : Scheme.{u}} {R S : CommRingCat.{u}} (a : Y ⟶ Spec S) (φ : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (a ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ a.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
end GroundTheory.Arith.SchemeCoh.ProjHom
