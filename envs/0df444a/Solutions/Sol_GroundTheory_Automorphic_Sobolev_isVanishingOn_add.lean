-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isVanishingOn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:05:45.371396+00:00
-- url     : https://prove2.me/submissions/b7aa79b7-2f20-4153-be53-456fda815921

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
theorem _root_.solution {u v : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U)
    (hv : Distribution.IsVanishingOn v U) : Distribution.IsVanishingOn (u + v) U := fun φ hφ ↦ by
  rw [add_apply, hu φ hφ, hv φ hφ, add_zero]
end GroundTheory.Automorphic.Sobolev
