-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.zero_padded_raw_packet_local_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T11:34:44.118264+00:00
-- url     : https://prove2.me/submissions/3d169960-7ffc-4736-aa98-045374df8ce4

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packet_coefficients_vanish
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coefficients_imply_local_power

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (R : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hR : 0 < R)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w (((n + m : ℕ) : ℝ) * R) r P = 0) :
    ∀ j : Fin K,
      P ∈ (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n := by
  have hcoeff :=
    OAI.PiExponent.LogarithmicJetIdeals.raw_packet_coefficients_vanish
      K v0 theta w (((n + m : ℕ) : ℝ) * R) r P hpacket
  exact OAI.PiExponent.LogarithmicJetIdeals.coefficients_imply_local_power
    K v0 theta w R r T e hR hv he hscale hT n P hcoeff