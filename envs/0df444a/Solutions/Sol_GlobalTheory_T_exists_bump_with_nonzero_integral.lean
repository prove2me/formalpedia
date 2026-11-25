-- Prove2me | solution 1 for GlobalTheory.T.exists_bump_with_nonzero_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:01.865207+00:00
-- url     : https://prove2.me/submissions/b90d5595-4b97-468d-83b7-cf93b0a8fa4f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsBumpWithNonzeroIntegral
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsBumpWithNonzeroIntegralStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_MeasureBump_exists_integral_ne_zero_of_carried_by_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X), IsOpen U → m Uᶜ = 0 → m ≠ 0 → (∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) → ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen | exact GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen | (intros; apply GlobalTheory.CompanionTheory.MeasureBump.exists_integral_ne_zero_of_carried_by_isOpen <;> assumption)
end _root_.GlobalTheory.T
