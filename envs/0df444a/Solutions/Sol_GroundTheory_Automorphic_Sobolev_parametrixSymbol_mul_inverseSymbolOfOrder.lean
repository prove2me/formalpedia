-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.parametrixSymbol_mul_inverseSymbolOfOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:32:52.603867+00:00
-- url     : https://prove2.me/submissions/2e28db4d-0bf0-453d-a266-e7596d396bfb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrixSymbol_mul_inverseSymbol

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
theorem _root_.solution {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (ξ : E) :
    symb0 c w ξ * qNSymb c w μ N ξ = 1 - rNSymb c w μ N ξ := by
  rw [qNSymb, ← mul_assoc, parametrixSymbol_mul_inverseSymbol c w hμ, rNSymb, mul_neg_geom_sum]
end GroundTheory.Automorphic.Sobolev
