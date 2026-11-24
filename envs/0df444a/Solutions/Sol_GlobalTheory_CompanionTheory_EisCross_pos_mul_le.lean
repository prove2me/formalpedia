-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisCross.pos_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:19.782811+00:00
-- url     : https://prove2.me/submissions/fdaf1d62-daff-42c8-b33a-7c7df3336eed

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.EisCross
theorem _root_.solution {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (C : Set G) (A : ℝ)
    (hA : ∀ g, ∀ u ∈ C, |l (g * u) - l g| ≤ A) (hc : Conv Δ P l) (y v : G) (hv : v ∈ C) :
    pos Δ P l (y * v) ≤ Real.exp A * pos Δ P l y := by
  unfold pos
  have hle : ∀ q : Cos P Δ, Real.exp (l (rep q * (y * v))) ≤ Real.exp A * Real.exp (l (rep q * y)) := by
    intro q
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hA (rep q * y) v hv
    rw [mul_assoc] at h
    have h' := (abs_le.mp h).2
    linarith
  have hs : Summable fun q : Cos P Δ => Real.exp A * Real.exp (l (rep q * y)) := (hc y).mul_left _
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hs) hs
end GlobalTheory.CompanionTheory.EisCross
