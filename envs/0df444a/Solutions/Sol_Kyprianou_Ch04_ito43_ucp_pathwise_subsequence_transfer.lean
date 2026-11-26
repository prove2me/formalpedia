-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ucp_pathwise_subsequence_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:57:27.931217+00:00
-- url     : https://prove2.me/submissions/3a3ebd5f-11c4-40cb-a6c9-62f6a418020c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_extract_ae_subsequence
import Theorems.Thm_Kyprianou_Ch04_ito43_uniform_sup_bound_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (A B : ℕ → NNReal → Omega → ℝ) (T : NNReal)
    (hA : ∀ (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |A n t w|}).toReal) atTop (nhds 0))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun w => sSup (Set.range (fun t : Set.Iic T => |B n t w|))) P)
    (hBdd : ∀ᵐ w ∂P, ∀ n, BddAbove (Set.range (fun t : Set.Iic T => |B n t w|)))
    (hTransfer : ∀ (N : ℕ → ℕ), Tendsto N atTop atTop →
      (∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |A (N n) t w| < e) →
      ∀ᵐ w ∂P, ∀ e : ℝ, 0 < e →
        ∀ᶠ n in atTop, ∀ t ≤ T, |B (N n) t w| < e) :
    ∀ (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |B n t w|}).toReal) atTop (nhds 0) := by
  intro e he
  apply Filter.tendsto_of_subseq_tendsto
  intro N hN
  obtain ⟨M,hM,hAE⟩ :=
    Kyprianou.Ch04.ito43_ucp_extract_ae_subsequence P A T hA N hN
  let L : ℕ → ℕ := fun n => N (M n)
  have hL : Tendsto L atTop atTop := hN.comp hM
  have hB := hTransfer L hL hAE
  let C : ℕ → Omega → ℝ := fun n w =>
    sSup (Set.range (fun t : Set.Iic T => |B (L n) t w|))
  have hsup : ∀ᵐ w ∂P, Tendsto (fun n => C n w) atTop (nhds 0) ∧
      ∀ n t, t ≤ T → |B (L n) t w| ≤ |C n w| := by
    filter_upwards [hBdd,hB] with w hw hb
    exact Kyprianou.Ch04.ito43_uniform_sup_bound_limit
      (fun n t => B (L n) t w) T (fun n => hw (L n)) hb
  have hlim : ∀ᵐ w ∂P, Tendsto (fun n => C n w) atTop (nhds 0) :=
    hsup.mono fun w hw => hw.1
  have hb : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |B (L n) t w| ≤ |C n w| :=
    hsup.mono fun w hw => hw.2
  exact ⟨M,Kyprianou.Ch04.ito43_ucp_countable_envelope P
    (fun n t w => B (L n) t w) C T (fun n => hMeas (L n)) hlim hb e he⟩
