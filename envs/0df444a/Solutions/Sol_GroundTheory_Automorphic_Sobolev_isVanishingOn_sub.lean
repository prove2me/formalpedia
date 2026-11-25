-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.isVanishingOn_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:43.646157+00:00
-- url     : https://prove2.me/submissions/015cc3b7-4565-4c0f-9498-db9ca7e4786b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_add
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_neg

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
    (hv : Distribution.IsVanishingOn v U) : Distribution.IsVanishingOn (u - v) U := by
  rw [sub_eq_add_neg]; exact isVanishingOn_add hu (isVanishingOn_neg hv)
end GroundTheory.Automorphic.Sobolev
