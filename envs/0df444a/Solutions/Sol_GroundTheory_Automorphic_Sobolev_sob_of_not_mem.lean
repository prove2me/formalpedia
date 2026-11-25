-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:15.199794+00:00
-- url     : https://prove2.me/submissions/ff8a36ad-4e12-44c6-a16e-5e439fc903b6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication

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
theorem _root_.solution {s : ℝ} {u : 𝓢'(E, ℂ)} (h : ¬ MemSobolev s 2 u) : sob s u = ⊤ := by rw [sob, dif_neg h]
end GroundTheory.Automorphic.Sobolev
