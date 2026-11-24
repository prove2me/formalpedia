-- Prove2me | solution 1 for GlobalTheory.T.frobeniusPowEquation_dvd_all_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:15.468832+00:00
-- url     : https://prove2.me/submissions/389d87b6-6a21-4073-bb8a-4eb7b3b9754c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPowStatement
import Theorems.Thm_GlobalTheory_phiEq_dvd_all_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.phiEq_dvd_all_pow | exact GlobalTheory.phiEq_dvd_all_pow | (intros; apply GlobalTheory.phiEq_dvd_all_pow <;> assumption)
end _root_.GlobalTheory.T
