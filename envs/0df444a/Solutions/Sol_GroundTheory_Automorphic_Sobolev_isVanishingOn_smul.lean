-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isVanishingOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:23:29.062811+00:00
-- url     : https://prove2.me/submissions/0fedf383-ad93-4d06-8b9b-26a43eac35fa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {u : 𝓢'(E, ℂ)} {U : Set E} (c : ℂ) (hu : Distribution.IsVanishingOn u U) :
    Distribution.IsVanishingOn (c • u) U := fun φ hφ ↦ by
  rw [smul_apply, hu φ hφ, smul_zero]
end GroundTheory.Automorphic.Sobolev
