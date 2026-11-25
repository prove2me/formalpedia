-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_of_sob_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:32:07.173436+00:00
-- url     : https://prove2.me/submissions/9026825f-65b6-449f-a148-9d0633074c29

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_lt_top_iff

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
theorem _root_.solution {s t : ℝ} {u v : 𝓢'(E, ℂ)} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : sob t v ≤ C * sob s u) (hu : MemSobolev s 2 u) : MemSobolev t 2 v :=
  sob_lt_top_iff.1 (h.trans_lt (ENNReal.mul_lt_top hC.lt_top (sob_lt_top_iff.2 hu)))
end GroundTheory.Automorphic.Sobolev
