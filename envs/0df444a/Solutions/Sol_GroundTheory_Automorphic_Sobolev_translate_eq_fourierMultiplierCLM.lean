-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.translate_eq_fourierMultiplierCLM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:49.542666+00:00
-- url     : https://prove2.me/submissions/5cfd30ca-3080-407f-b636-fa708e28b71e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_translate_apply_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_expChar_smul_fourierInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (h : E) (u : 𝓢'(E, F)) :
    translate F h u = fourierMultiplierCLM F (expChar (-h)) u := by
  ext φ
  rw [translate_apply_apply, fourierMultiplierCLM_apply_apply, fourier_expChar_smul_fourierInv]
end GroundTheory.Automorphic.Sobolev
