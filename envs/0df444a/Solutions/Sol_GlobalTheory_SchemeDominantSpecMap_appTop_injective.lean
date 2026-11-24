-- Prove2me | solution 1 for GlobalTheory.SchemeDominantSpecMap.appTop_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:51.121519+00:00
-- url     : https://prove2.me/submissions/aa82bfa8-a9ef-46f5-8f3f-32e7e3bb684e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.SchemeDominantSpecMap
namespace GlobalTheory.SchemeDominantSpecMap
theorem _root_.solution {R A : CommRingCat.{u_1}} (φ : R ⟶ A) (h : Function.Injective φ) :
    Function.Injective (Spec.map φ).appTop := by

  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality φ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1.comp
    (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)
end GlobalTheory.SchemeDominantSpecMap
