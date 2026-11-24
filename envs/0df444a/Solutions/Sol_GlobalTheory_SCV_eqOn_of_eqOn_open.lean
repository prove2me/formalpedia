-- Prove2me | solution 1 for GlobalTheory.SCV.eqOn_of_eqOn_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:28:45.144262+00:00
-- url     : https://prove2.me/submissions/d9df312f-f178-48ee-9a8d-040f1a043381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f g : E → V} {U W : Set E} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hW : IsOpen W)
    (hne : W.Nonempty) (hWU : W ⊆ U) (hfg : EqOn f g W) : EqOn f g U := by
  obtain ⟨c, hc⟩ := hne
  exact eqOn_of_eventuallyEq hU hU' hf hg (hWU hc)
    (hfg.eventuallyEq_of_mem (hW.mem_nhds hc))
end GlobalTheory.SCV
