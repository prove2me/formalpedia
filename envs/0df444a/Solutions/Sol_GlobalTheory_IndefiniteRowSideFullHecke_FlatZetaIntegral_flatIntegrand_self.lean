-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:34.030095+00:00
-- url     : https://prove2.me/submissions/41915129-4c66-42fc-bab9-858e6445517b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
omit [MeasurableSpace X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
theorem _root_.solution (f : X → ℂ) (a : X → ℝ) (s₀ : ℂ) : flatIntegrand f a s₀ s₀ = f := by
  funext x
  simp [flatIntegrand]
end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
