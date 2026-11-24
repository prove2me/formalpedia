-- Prove2me | solution 2 for Kyprianou.Ch03.rawRightGermRestrictedVersionLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:57.560193+00:00
-- url     : https://prove2.me/submissions/7eab6e77-e806-4ecc-bac5-b3c22bbb1585

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_rawNaturalEventAETransferV1
import Theorems.Thm_Kyprianou_Ch03_rawNaturalDeterministicRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovPathLawOfCommonAELimitsV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y : NNReal → Omega → ℝ) (hY : IsLevyProcess Y P)
    (hMeas : ∀ t, Measurable (Y t))
    (hEq : ∀ᵐ w ∂P, ∀ u, Y u w = X u w)
    (t : NNReal) (A : Set Omega)
    (hA : MeasurableSet[⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s] A) :
    Measure.map (fun (w : Omega) (u : NNReal) => Y (t + u) w - Y t w) (P.restrict A) =
      P A • Measure.map (fun (w : Omega) (u : NNReal) => Y u w) P := by
  obtain ⟨s, _, hs, hst⟩ := exists_seq_strictAnti_tendsto t
  let U (n : ℕ) (w : Omega) (u : NNReal) := Y (s n + u) w - Y (s n) w
  let V (w : Omega) (u : NNReal) := Y (t + u) w - Y t w
  have hU (n : ℕ) : Measurable (U n) :=
    measurable_pi_iff.mpr fun u => (hMeas _).sub (hMeas _)
  have hLaw (n : ℕ) : Measure.map (U n) (P.restrict A) =
      P A • Measure.map (fun w u => Y u w) P := by
    have hle : (⨅ r : NNReal, ⨅ (_ : t < r), PerfCorrMSQ.natFiltr X r) ≤
        PerfCorrMSQ.natFiltr X (s n) := by
      refine (iInf_le (fun r : NNReal => ⨅ (_ : t < r), PerfCorrMSQ.natFiltr X r) (s n)).trans ?_
      exact iInf_le (fun _ : t < s n => PerfCorrMSQ.natFiltr X (s n)) (hs n)
    have hAs : MeasurableSet[PerfCorrMSQ.natFiltr X (s n)] A := hle A hA
    obtain ⟨B, hB, hAB⟩ := Kyprianou.Ch03.rawNaturalEventAETransferV1 P X Y hEq (s n) A hAs
    rw [Measure.restrict_congr_set hAB, measure_congr hAB]
    exact Kyprianou.Ch03.rawNaturalDeterministicRestrictedPathV1 P Y hY hMeas (s n) B hB
  have hlim : ∀ᵐ w ∂(P.restrict A), ∀ u : NNReal,
      Tendsto (fun n => U n w u) atTop (𝓝 (V w u)) := by
    have hc : ∀ᵐ w ∂(P.restrict A), IsCadlag (fun t => Y t w) :=
      ae_restrict_of_ae hY.cadlag_ae
    filter_upwards [hc] with w hw
    intro u
    have hst' : Tendsto s atTop (𝓝[≥] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hst, Eventually.of_forall fun n => (hs n).le⟩
    have hsu : Tendsto (fun n => s n + u) atTop (𝓝[≥] (t+u)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hst.add_const u,
        Eventually.of_forall fun n => by simpa [add_comm] using add_le_add_right (hs n).le u⟩
    exact (((hw (t+u)).1.tendsto.comp hsu).sub ((hw t).1.tendsto.comp hst'))
  exact (Kyprianou.Ch03.strongMarkovPathLawOfCommonAELimitsV1 (P.restrict A) U V _
    hU hLaw hlim).2
