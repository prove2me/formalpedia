-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDuality_dyadicPairLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T11:47:46.8883+00:00
-- url     : https://prove2.me/submissions/4062e4ec-fafa-4e6d-878f-497ca98537fa

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_supInfDyadicGridArithmeticV1
import Theorems.Thm_Kyprianou_Ch03_supInfGridReflectedVectorLawV1
import Theorems.Thm_Kyprianou_Ch03_supInfFiniteVectorPairTransferV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (n : ℕ) :
    Measure.map
      (fun omega : Omega =>
        let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (a, a - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (X t omega - b, -b)) P := by
  let q (i : Fin (2 ^ n + 1)) := (i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))
  obtain ⟨hq, hq0, hlast, hqt, hrev⟩ := Kyprianou.Ch03.supInfDyadicGridArithmeticV1 t n
  change q 0 = 0 at hq0
  change q (Fin.last (2 ^ n)) = t at hlast
  change ∀ i, q i.rev = t - q i at hrev
  let V (ω : Omega) (i : Fin (2 ^ n + 1)) := X (q i) ω
  have hc := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  have hm : AEMeasurable V P := aemeasurable_pi_iff.mpr fun i => hc (q i)
  have hz (ω : Omega) : V ω 0 = 0 := by
    change X (q 0) ω = 0
    simp only [hq0, hX.start_zero]
  have h := Kyprianou.Ch03.supInfGridReflectedVectorLawV1 P X hX t (2 ^ n)
    q hq hq0 hqt
  have he : (fun ω : Omega => fun i : Fin (2 ^ n + 1) =>
      X t ω - X (t - q i) ω) =
      (fun ω : Omega => fun i : Fin (2 ^ n + 1) =>
        V ω (Fin.last (2 ^ n)) - V ω i.rev) := by
    funext ω i
    change X t ω - X (t - q i) ω = X (q (Fin.last (2 ^ n))) ω - X (q i.rev) ω
    rw [hlast, hrev]
  rw [he] at h
  have hh := Kyprianou.Ch03.supInfFiniteVectorPairTransferV1 P (2 ^ n) V hm hz h
  simpa only [V, hlast] using hh
