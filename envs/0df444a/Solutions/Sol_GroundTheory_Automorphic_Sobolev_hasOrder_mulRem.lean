-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.hasOrder_mulRem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:23.866647+00:00
-- url     : https://prove2.me/submissions/e6abf858-b61d-4467-8871-41d855a82867

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_commConst_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_mulRem_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_wInt_nonneg


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
theorem _root_.solution (χ : 𝓢(E, ℂ)) (r : ℝ) : HasOrder (mulRem χ r) (-1) := fun s ↦
  ⟨commConst r (s + 1 - r) * wInt ((|s + 1 - r| + |r - 1| + 1) / 2) (𝓕 χ),
    mul_nonneg (commConst_nonneg _ _) (wInt_nonneg _ _), fun u hu ↦ by
    have h := sob_mulRem_le χ r (s + 1 - r) (u := u) (by convert hu using 2; ring)
    rwa [show r + (s + 1 - r) = s - -1 by ring, show s - -1 - 1 = s by ring] at h⟩
end GroundTheory.Automorphic.Sobolev
