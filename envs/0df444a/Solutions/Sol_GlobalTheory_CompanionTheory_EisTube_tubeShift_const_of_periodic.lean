-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.tubeShift_const_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:13.826625+00:00
-- url     : https://prove2.me/submissions/dd8beaff-18a2-4dfa-bf8d-90580d90fb7b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution (U : Set ℂ) (hU : IsOpen U) (hc : IsPreconnected U)
    (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ U)
    (hper : ∀ w ∈ U, ∀ s : ℝ, Φ (w + (s : ℂ) * Complex.I) = Φ w)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) : Φ a = Φ b := by
  have hz : U.EqOn (deriv Φ) 0 := by
    intro w hw
    have h1 : HasDerivAt Φ (deriv Φ w) (w + ((0 : ℝ) : ℂ) * Complex.I) := by
      simpa using (hd.differentiableAt (hU.mem_nhds hw)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add w
    have h3 := HasDerivAt.scomp (0 : ℝ) h1 h2
    have h4 : HasDerivAt (Φ ∘ fun s : ℝ => w + (s : ℂ) * Complex.I) 0 0 := by
      have : (Φ ∘ fun s : ℝ => w + (s : ℂ) * Complex.I) = fun _ => Φ w :=
        funext fun s => hper w hw s
      rw [this]
      exact hasDerivAt_const _ _
    have := h3.unique h4
    simpa using this
  exact hU.is_const_of_deriv_eq_zero hc hd hz ha hb
end GlobalTheory.CompanionTheory.EisTube
