-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.prod_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:56.395391+00:00
-- url     : https://prove2.me/submissions/6a13bbb6-8208-46e0-8a6f-2121ad22f844

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B₁ B₂ : InvAlg K) : (B₁.prod B₂).P = B₁.P * B₂.P := by
  have : LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A) =
      (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
    ext <;> simp
  have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
  rw [← this] at h2
  exact h2
end GlobalTheory.UnitLemma.Orbit
