-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.qNSymb_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:25.432506+00:00
-- url     : https://prove2.me/submissions/dac21b7b-e5e9-40ec-ae81-a933bfeba425

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rhoSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum


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
theorem _root_.solution (μ : ℝ) (N : ℕ) : (qNSymb c w μ N).HasTemperateGrowth :=
  (qSymb_hasTemperateGrowth c w μ).mul
    (Function.HasTemperateGrowth.sum fun j _ ↦ (rhoSymb_hasTemperateGrowth c w μ).pow j)
end GroundTheory.Automorphic.Sobolev
