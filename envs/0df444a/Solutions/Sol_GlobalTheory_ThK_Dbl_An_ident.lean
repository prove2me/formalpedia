-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.ident
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:09.918188+00:00
-- url     : https://prove2.me/submissions/c900f257-caf7-4c4e-a857-6554d69d2a54

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FarRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}
namespace GlobalTheory.ThK.Dbl.An
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {g g' : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg' : DifferentiableOn ℂ g' U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ g s = g' s) {s : ℂ} (hs : s ∈ U) : g s = g' s := by
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg'.analyticOnNhd hU) hc (h _ h1).1 ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz using (h z hz).2
end GlobalTheory.ThK.Dbl.An
