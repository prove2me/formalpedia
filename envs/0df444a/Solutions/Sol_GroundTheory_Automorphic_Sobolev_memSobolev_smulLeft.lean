-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_smulLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:33.304215+00:00
-- url     : https://prove2.me/submissions/4732724d-d805-4b3a-b005-250f4b19dda2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_lt_top_iff
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_smulLeft_le

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ : 𝓢(E, ℂ)) {r : ℝ} {u : 𝓢'(E, ℂ)} (hu : MemSobolev r 2 u) :
    MemSobolev r 2 (smulLeftCLM ℂ (χ : E → ℂ) u) :=
  sob_lt_top_iff.1 ((sob_smulLeft_le χ r hu).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sob_lt_top_iff.2 hu)))
end GroundTheory.Automorphic.Sobolev
