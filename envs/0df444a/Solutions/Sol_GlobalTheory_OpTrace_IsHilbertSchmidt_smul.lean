-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsHilbertSchmidt.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:32.161237+00:00
-- url     : https://prove2.me/submissions/aec7bbc1-1168-4f9e-a5c6-d2afc00194bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}
omit [CompleteSpace K]
namespace GlobalTheory.OpTrace
namespace IsHilbertSchmidt
theorem _root_.solution {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (c : ℂ) :
    IsHilbertSchmidt (c • T) :=
  h.of_norm_le ‖c‖ fun x => by simp [norm_smul]
end IsHilbertSchmidt
end GlobalTheory.OpTrace
