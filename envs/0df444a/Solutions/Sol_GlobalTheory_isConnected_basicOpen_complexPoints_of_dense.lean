-- Prove2me | solution 1 for GlobalTheory.isConnected_basicOpen_complexPoints_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:32.132632+00:00
-- url     : https://prove2.me/submissions/212a2706-c65e-4f36-9dfe-61fb544d3fc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedBasicOpenComplexPointsOfDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) →
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) →
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf

  obtain ⟨h, hh, hconn⟩ := H1 A f hf
  have hhf : h * f ≠ 0 := mul_ne_zero hh hf

  apply hconn.subset_closure
  · rintro x ⟨φ, rfl, hx⟩
    refine ⟨φ, rfl, ?_⟩
    rw [map_mul] at hx
    exact right_ne_zero_of_mul hx
  · rintro x ⟨φ, rfl, -⟩
    exact H2 A (h * f) hhf ⟨φ, rfl, by simp⟩
end GlobalTheory
