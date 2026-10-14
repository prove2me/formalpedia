-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.zero_padded_raw_packet_mem_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T23:14:26.468824+00:00
-- url     : https://prove2.me/submissions/bd9b21cb-a587-408c-b10a-39a916d58727
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_zero_padded_raw_packet_local_power
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_distinct_local_jet_ideals_isCoprime
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_mem_iInf_pow_of_pairwise_isCoprime

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
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w (((n + m : ℕ) : ℝ) * R) r P = 0) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by
  have hlocal :=
    OAI.PiExponent.LogarithmicJetIdeals.zero_padded_raw_packet_local_power
      K v0 theta w R r T e hR hv he hscale hT n P hpacket
  have hcoprime :=
    OAI.PiExponent.LogarithmicJetIdeals.distinct_local_jet_ideals_isCoprime
      K r T e hc
  have hpower :
      P ∈ (⨅ j : Fin K, localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n :=
    OAI.PiExponent.LogarithmicJetIdeals.mem_iInf_pow_of_pairwise_isCoprime
      K n (fun j : Fin K => localJetIdeal (fun i => (j.val : ℂ) * r i) T e)
      hcoprime (x := P) hlocal
  simpa [simultaneousJetIdeal] using hpower