-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.parametrixSymbol_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:16:02.791214+00:00
-- url     : https://prove2.me/submissions/1b283c3d-2fe5-4157-9a86-971647253425

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_constSymb_hasTemperateGrowth


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
theorem _root_.solution : (symb0 c w).HasTemperateGrowth :=
  constSymb_hasTemperateGrowth w c
end GroundTheory.Automorphic.Sobolev
