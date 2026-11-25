-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.qSymb_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:38.141675+00:00
-- url     : https://prove2.me/submissions/a633e63f-4211-46bb-ac5d-5e70105180e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrixSymbol_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rhoSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_comp
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_comp


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
theorem _root_.solution (μ : ℝ) : (qSymb c w μ).HasTemperateGrowth := by
  have h : (fun ξ ↦ starRingEnd ℂ (symb0 c w ξ)).HasTemperateGrowth :=
    (Complex.conjCLE.hasTemperateGrowth).comp (parametrixSymbol_hasTemperateGrowth c w)
  exact ((Function.HasTemperateGrowth.const _).mul h).mul (rhoSymb_hasTemperateGrowth c w μ)
end GroundTheory.Automorphic.Sobolev
