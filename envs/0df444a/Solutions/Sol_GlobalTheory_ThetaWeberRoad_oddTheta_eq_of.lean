-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.oddTheta_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:37:18.777885+00:00
-- url     : https://prove2.me/submissions/dfbc03d5-497b-41b0-8f34-c9c820e580c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad
namespace GlobalTheory.ThetaWeberRoad
theorem _root_.solution (τ : UpperHalfPlane) (z w k : ℂ)
    (h : jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ = cexp k * jacobiTheta₂ w τ) :
    oddTheta τ z = cexp ((π : ℂ) * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2) + k) * jacobiTheta₂ w τ := by
  unfold oddTheta
  rw [h, ← mul_assoc, ← Complex.exp_add]
end GlobalTheory.ThetaWeberRoad
