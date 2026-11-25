-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_limPunctured
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:42.054802+00:00
-- url     : https://prove2.me/submissions/8f8ebf32-19af-400b-a707-d1c2b7668513

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Theorems.Thm_GroundTheory_Global_Elliptic_tendsto_limPunctured
import Theorems.Thm_GroundTheory_Global_Elliptic_limPunctured_eventuallyEq_of_analyticAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution [CompleteSpace E] {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z)
    (ho : 0 ≤ meromorphicOrderAt f z) : AnalyticAt ℂ (limPunctured f) z := by
  have hev : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f w := hf.eventually_analyticAt
  have heq : limPunctured f =ᶠ[𝓝[≠] z] f :=
    hev.mono fun w hw ↦ (limPunctured_eventuallyEq_of_analyticAt hw).eq_of_nhds
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · exact hev.mono fun w hw ↦
      hw.differentiableAt.congr_of_eventuallyEq (limPunctured_eventuallyEq_of_analyticAt hw)
  · rw [← continuousWithinAt_compl_self]
    exact (tendsto_limPunctured hf ho).congr' heq.symm
end GroundTheory.Global.Elliptic
