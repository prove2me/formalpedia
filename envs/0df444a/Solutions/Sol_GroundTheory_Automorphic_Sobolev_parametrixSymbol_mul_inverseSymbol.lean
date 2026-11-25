-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.parametrixSymbol_mul_inverseSymbol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:10.393078+00:00
-- url     : https://prove2.me/submissions/db1c7d8c-1328-430f-bb30-b8ead5676b6a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rhoSymb_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    symb0 c w ξ * qSymb c w μ ξ = 1 - rhoSymb c w μ ξ := by
  rw [qSymb, rhoSymb_eq c w hμ]
  have hpos : (0 : ℝ) < 1 + μ * ‖symb0 c w ξ‖ ^ 2 := by positivity
  have hmc : symb0 c w ξ * starRingEnd ℂ (symb0 c w ξ) = ((‖symb0 c w ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc symb0 c w ξ * ((μ : ℂ) * starRingEnd ℂ (symb0 c w ξ) *
        (((1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ))
      = (μ : ℂ) * (symb0 c w ξ * starRingEnd ℂ (symb0 c w ξ)) *
          (((1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by ring
    _ = (((μ * ‖symb0 c w ξ‖ ^ 2) * (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
        rw [hmc]; push_cast; ring
    _ = ((1 - (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
        congr 1; field_simp; ring
    _ = _ := by push_cast; ring
end GroundTheory.Automorphic.Sobolev
