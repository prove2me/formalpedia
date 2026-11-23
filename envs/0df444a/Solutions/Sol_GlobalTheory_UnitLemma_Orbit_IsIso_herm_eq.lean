-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.IsIso.herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:39.449085+00:00
-- url     : https://prove2.me/submissions/384a2f08-b469-40a3-abaf-b734dfa73f01

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
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}
namespace GlobalTheory.UnitLemma.Orbit.IsIso
theorem _root_.solution (h : IsIso φ) (x y z : B.A) : C.herm (φ x) (φ y) (φ z) = B.herm x y z := by
  unfold InvAlg.herm
  rw [← h.1, ← map_mul, ← map_mul, Algebra.trace_eq_of_algEquiv]
end GlobalTheory.UnitLemma.Orbit.IsIso
