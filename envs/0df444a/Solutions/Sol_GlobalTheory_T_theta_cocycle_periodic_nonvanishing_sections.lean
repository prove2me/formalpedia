-- Prove2me | solution 1 for GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:27.781899+00:00
-- url     : https://prove2.me/submissions/a3fc4bd8-0e4d-40bd-939f-495c7dd6c806

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSectionsStatement
import Theorems.Thm_GlobalTheory_PeriodSymm_period_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  first | exact @GlobalTheory.PeriodSymm.period_symm | exact GlobalTheory.PeriodSymm.period_symm | (intros; apply GlobalTheory.PeriodSymm.period_symm <;> assumption)
end _root_.GlobalTheory.T
