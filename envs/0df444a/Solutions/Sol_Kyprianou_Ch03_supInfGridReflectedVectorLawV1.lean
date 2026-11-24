-- Prove2me | solution 1 for Kyprianou.Ch03.supInfGridReflectedVectorLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:00:59.926178+00:00
-- url     : https://prove2.me/submissions/45217dfd-bc06-40c4-b70a-5d4c654b33d9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_levyReflectedIncrementVectorLawV1
import Theorems.Thm_Kyprianou_Ch03_finiteZeroBasedVectorLawOfReverseDifferencesV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (m : ℕ) (q : Fin (m + 1) → NNReal) (hq : Monotone q)
    (hq0 : q 0 = 0) (hqt : ∀ i, q i ≤ t) :
    P.map (fun ω : Omega => fun i => X (q i) ω) =
    P.map (fun ω : Omega => fun i => X t ω - X (t - q i) ω) := by
  let F (ω : Omega) (i : Fin (m + 1)) := X (q i) ω
  let G (ω : Omega) (i : Fin (m + 1)) := X t ω - X (t - q i) ω
  have hc := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  apply Kyprianou.Ch03.finiteZeroBasedVectorLawOfReverseDifferencesV1 P m
  · exact aemeasurable_pi_iff.mpr fun i => hc (q i)
  · exact aemeasurable_pi_iff.mpr fun i => (hc t).sub (hc (t - q i))
  · intro ω
    simp [F, hq0, hX.start_zero]
  · intro ω
    simp [G, hq0]
  · let N (v : Fin m → ℝ) (i : Fin m) := -v i
    have hm : Measurable N :=
      measurable_pi_iff.mpr fun i => (measurable_pi_apply i).neg
    let U (ω : Omega) (i : Fin m) :=
      X (t - q i.castSucc) ω - X (t - q i.succ) ω
    let V (ω : Omega) (i : Fin m) :=
      X (q i.succ) ω - X (q i.castSucc) ω
    have hu : AEMeasurable U P :=
      aemeasurable_pi_iff.mpr fun i => (hc _).sub (hc _)
    have hv : AEMeasurable V P :=
      aemeasurable_pi_iff.mpr fun i => (hc _).sub (hc _)
    have h := congrArg (Measure.map N)
      (Kyprianou.Ch03.levyReflectedIncrementVectorLawV1 P X hX t m q hq hqt)
    change Measure.map N (P.map U) = Measure.map N (P.map V) at h
    rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hu,
      AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hv] at h
    have eF : (fun ω i => F ω i.castSucc - F ω i.succ) = N ∘ V := by
      funext ω i
      dsimp [F, N, V, Function.comp_def]
      ring
    have eG : (fun ω i => G ω i.castSucc - G ω i.succ) = N ∘ U := by
      funext ω i
      dsimp [G, N, U, Function.comp_def]
      ring
    change P.map (fun (ω : Omega) (i : Fin m) => F ω i.castSucc - F ω i.succ) =
      P.map (fun (ω : Omega) (i : Fin m) => G ω i.castSucc - G ω i.succ)
    rw [eF, eG]
    exact h.symm
