-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.raw_packet_zero_of_mem_simultaneousJetIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T11:33:12.95175+00:00
-- url     : https://prove2.me/submissions/d845ba17-c312-47d9-9fc2-b76d0326a0c2

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_jetCoordinate_pow_coeff_zero_of_weight_lt
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_rawPacketMap_zero_of_ideal_power_generator_order

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

 theorem solution
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
      (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (simultaneousJetIdeal K r T e) ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * S) r P = (fun _ => 0) := by
  apply OAI.PiExponent.LogarithmicJetIdeals.rawPacketMap_zero_of_ideal_power_generator_order
    (K := K) (v0 := v0) (theta := theta) (w := w) (r := r)
    (T := T) (e := e) (S := S) (n := n) (P := P)
    hweights
  intro j i a ha
  exact OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_pow_coeff_zero_of_weight_lt
    K v0 theta w r T e S hweights he hcommon hT j i a ha
  exact hP