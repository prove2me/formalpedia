-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sob_lt_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:23:19.720937+00:00
-- url     : https://prove2.me/submissions/89d756e2-c693-4b59-9d90-3a755c3eae08

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_of_not_mem

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
theorem _root_.solution {s : ℝ} {u : 𝓢'(E, ℂ)} : sob s u < ⊤ ↔ MemSobolev s 2 u := by
  constructor
  · intro h; by_contra hc; rw [sob_of_not_mem hc] at h; exact lt_irrefl _ h
  · intro h; rw [sob_of_mem h]; exact enorm_lt_top
end GroundTheory.Automorphic.Sobolev
