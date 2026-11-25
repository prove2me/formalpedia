-- Prove2me | solution 1 for GlobalTheory.T.poisson_summation_thetaSeriesRowTerm_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:18.392662+00:00
-- url     : https://prove2.me/submissions/88cdd568-e443-417b-9d60-5b6fd83ed761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Theorems.Thm_GlobalTheory_SW_FourierJ_Row_poisson_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℕ), 0 < R → ∀ τ ∈ Siegel ι, -τ⁻¹ ∈ Siegel ι → IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧ ∀ (a : ι → ℚ) (ζ : ι → ℂ), (Summable fun m : ι → ℤ => ‖gs τ ζ (a + (R : ℚ) • zv m)‖) ∧ (Summable fun m : ι → ℤ => ‖gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m)‖) ∧ cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * ∑' m : ι → ℤ, gs τ ζ (a + (R : ℚ) • zv m) = c * ∑' m : ι → ℤ, ech (a ⬝ᵥ ((R : ℚ)⁻¹ • zv m)) * gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m) := by
  first | exact @GlobalTheory.SW.FourierJ.Row.poisson_class | exact GlobalTheory.SW.FourierJ.Row.poisson_class | (intros; apply GlobalTheory.SW.FourierJ.Row.poisson_class <;> assumption)
end _root_.GlobalTheory.T
