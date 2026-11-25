-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.parametrix_comp_frozenOperator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:13.990091+00:00
-- url     : https://prove2.me/submissions/c6405f22-963a-446c-9ff9-f82f1db79fb7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrixSymbol_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_constOp_eq_symb0
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qNSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rNSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrixSymbol_mul_inverseSymbolOfOrder
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierMultiplierCLM_one_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_id


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
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (x₀ : E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    Qop a w x₀ μ k ∘L P0 a w x₀ = ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - Rop a w x₀ μ k := by
  rw [Qop, P0, constOp_eq_symb0, fourierMultiplierCLM_compL_fourierMultiplierCLM
    (parametrixSymbol_hasTemperateGrowth _ w) (qNSymb_hasTemperateGrowth _ w μ k), Rop,
    ← fourierMultiplierCLM_one_sub (rNSymb_hasTemperateGrowth _ w μ k)]
  congr 1; ext ξ
  exact parametrixSymbol_mul_inverseSymbolOfOrder _ w hμ k ξ
end GroundTheory.Automorphic.Sobolev
