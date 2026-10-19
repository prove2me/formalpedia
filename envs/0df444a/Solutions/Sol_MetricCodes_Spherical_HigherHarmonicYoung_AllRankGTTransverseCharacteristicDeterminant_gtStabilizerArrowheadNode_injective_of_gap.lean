-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.gtStabilizerArrowheadNode_injective_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/ed484515-3b5d-4edd-bfcb-728ab275e1e4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
theorem _root_.solution
    {r : ℕ} (rho : ℝ) (M : Fin r → ℝ)
    (hrho : 0 < rho)
    (hgap : ∀ i : Fin r, rho + 1 / 2 ≤ M i)
    (hinj : Function.Injective M) :
    Function.Injective (gtStabilizerArrowheadNode rho M) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => cases x; cases y; rfl
      | inr y =>
          rcases y with ⟨j, b⟩
          cases b <;>
            simp only [gtStabilizerArrowheadNode] at hxy <;>
            linarith [hgap j]
  | inr x =>
      rcases x with ⟨i, a⟩
      cases y with
      | inl y =>
          cases a <;>
            simp only [gtStabilizerArrowheadNode] at hxy <;>
            linarith [hgap i]
      | inr y =>
          rcases y with ⟨j, b⟩
          cases a <;> cases b
          · have heq : M i = M j := by
              simp only [gtStabilizerArrowheadNode] at hxy
              linarith
            have hij := hinj heq
            subst j
            rfl
          · simp only [gtStabilizerArrowheadNode] at hxy
            linarith [hgap i, hgap j]
          · simp only [gtStabilizerArrowheadNode] at hxy
            linarith [hgap i, hgap j]
          · have heq : M i = M j := by
              simp only [gtStabilizerArrowheadNode] at hxy
              linarith
            have hij := hinj heq
            subst j
            rfl
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
