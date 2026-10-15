-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.raw_packet_coefficients_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T13:42:04.893456+00:00
-- url     : https://prove2.me/submissions/0900196a-d782-4190-b917-7ed59bf73bb9

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w H r P = 0) :
    ∀ j : Fin K, ∀ a : Fin (m + 1) → ℕ,
      a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet
          (fun i => (j.val : ℂ) * r i) P) = 0 := by
  intro j a ha
  have h := congrFun hpacket (j, ⟨a, ha⟩)
  simpa [rawPacketMap] using h