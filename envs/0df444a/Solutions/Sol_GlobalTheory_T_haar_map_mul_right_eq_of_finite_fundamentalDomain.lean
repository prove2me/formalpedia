-- Prove2me | solution 1 for GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:06:53.051846+00:00
-- url     : https://prove2.me/submissions/b65f3881-73f2-41ef-b448-12c30175b78e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapMulRightEqOfFiniteFundamentalDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMapMulRightEqOfFiniteFundamentalDomainStatement
import Theorems.Thm_GlobalTheory_haar_map_mul_right_eq_of_fundamentalDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ n₀ : N, κ.map (· * n₀) = κ := by
  first | exact @GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | exact GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | (intros; apply GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain <;> assumption)
end _root_.GlobalTheory.T
