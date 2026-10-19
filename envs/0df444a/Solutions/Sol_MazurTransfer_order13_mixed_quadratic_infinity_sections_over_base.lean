-- Prove2me | solution 1 for MazurTransfer.order13_mixed_quadratic_infinity_sections_over_base
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T04:42:56.416691+00:00
-- url     : https://prove2.me/submissions/9053f147-ee6f-4558-9f63-c38452b5a501

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two actual coefficient-ring sections of the mixed
quadratic glued curve, with reciprocal coordinates (0,0) and (0,-1).
Named downstream consumer: rigidification of its integral Picard family.
Their comparison with the existing rational infinity sections is separate.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalInfinitySectionsData20261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticInfinitySections Order13MixedQuadraticGluedCurve
universe u
namespace MazurTransfer.Order13MixedQuadraticInfinitySectionOriginalInterface20261019
end MazurTransfer.Order13MixedQuadraticInfinitySectionOriginalInterface20261019
theorem solution : (∀ (R : Type u) [CommRing R], infinitySectionZero R ≫ curveToBase R = 𝟙 (Spec (.of R))) ∧ (∀ (R : Type u) [CommRing R], infinitySectionNegOne R ≫ curveToBase R = 𝟙 (Spec (.of R))) := by
  exact ⟨infinitySectionZero_comp,infinitySectionNegOne_comp⟩
#print axioms solution
