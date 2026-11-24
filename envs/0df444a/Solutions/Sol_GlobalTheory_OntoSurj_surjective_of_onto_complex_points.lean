-- Prove2me | solution 1 for GlobalTheory.OntoSurj.surjective_of_onto_complex_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:34:03.978783+00:00
-- url     : https://prove2.me/submissions/2a769b59-1f4f-4e32-b6c9-610ead86571c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ProdSurjectiveGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AbelianSchemeSurjectiveOfOntoComplexPoints
import Theorems.Thm_GlobalTheory_OntoSurj_surjective_of_points
import Theorems.Thm_GlobalTheory_GeomSurj_exists_lift_of_surjective
import Theorems.Thm_GlobalTheory_GeomSurj_surjective_of_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.OntoSurj
namespace GlobalTheory.OntoSurj
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by
  intro R _ _ σ hσ A B _ _ Φ hA hB h
  have := hB.proper
  have := hA.proper
  have := hA.smooth
  have hpr : IsProper Φ.left := by
    have : IsProper (Φ.left ≫ A.hom) := by rwa [Over.w]
    exact IsProper.of_comp Φ.left A.hom
  have hs : Surjective Φ.left := by
    refine surjective_of_points σ hσ A.hom A.hom.isOpenMap Φ.left
      Φ.left.isClosedMap.isClosed_range fun y hy ↦ ?_
    obtain ⟨p, hp⟩ := h (Over.homMk y hy)
    exact ⟨p.left, congrArg (·.left) hp⟩
  refine ⟨hs, fun k _ _ t y ↦ ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y
end GlobalTheory.OntoSurj
