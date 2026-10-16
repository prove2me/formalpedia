-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.padded_packet_kernel_in_simultaneous_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:55:42.224222+00:00
-- url     : https://prove2.me/submissions/078fbbdd-1b58-4cf5-87c1-e508e643398f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packet_zero_implies_weighted_formalJet_coeff_zero
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_simultaneous_power

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w (((n + m : ℕ) : ℝ) * S) r P = 0) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by
  apply OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_simultaneous_power
    K v0 theta w S r T e hS hv he hscale hT hc n P
  intro j a ha
  exact OAI.PiExponent.LogarithmicJetIdeals.raw_packet_zero_implies_weighted_formalJet_coeff_zero
    K v0 theta w (((n + m : ℕ) : ℝ) * S) r P hpacket j a ha
