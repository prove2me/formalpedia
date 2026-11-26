-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ExtendedStoppedPathLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:00:14.472805+00:00
-- url     : https://prove2.me/submissions/1fb4462c-a2b1-420c-8c67-4938d8761fb8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46DeterministicRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch04_exercise46RightGridFutureLimitV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedUpperGridV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridRestrictedLawV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovPathLawOfCommonAELimitsV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (tau : Omega → WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)) :
    AEMeasurable (fun omega : Omega => fun u : NNReal =>
      L.X (finiteTime omega + u) omega - L.X (finiteTime omega) omega)
      (P.restrict {omega : Omega | tau omega ≠ ⊤}) ∧
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map (fun omega : Omega => fun u : NNReal =>
        L.X (finiteTime omega + u) omega - L.X (finiteTime omega) omega)
        (P.restrict (B ∩ {omega : Omega | tau omega ≠ ⊤})) =
      P (B ∩ {omega : Omega | tau omega ≠ ⊤}) • Measure.map (fun omega u => L.X u omega) P := by
  classical
  letI : IsProbabilityMeasure P := L.isProbability
  have hAdapt : ∀ t : NNReal, Measurable[F t] (L.X t) := L.adapted
  have hDet := Kyprianou.Ch04.exercise46DeterministicRestrictedPathV1 P F L
  have hMeas : ∀ t : NNReal, Measurable (L.X t) :=
    fun t => (hAdapt t).mono (F.le t) le_rfl
  obtain ⟨T, hCount, hFib, hZero, hT⟩ :=
    strongMarkovExtendedUpperGridV1 F tau hTau finiteTime hFiniteTime
  let D : Set Omega := {w | tau w ≠ ⊤}
  let Y : ℕ → Omega → (NNReal → ℝ) :=
    fun n w u => L.X (T n w + u) w - L.X (T n w) w
  let Z : Omega → (NNReal → ℝ) :=
    fun w u => L.X (finiteTime w + u) w - L.X (finiteTime w) w
  let nu := Measure.map (fun w u => L.X u w) P
  have hGrid := fun n => strongMarkovCountableGridRestrictedLawV1 F tau hTau
    finiteTime hFiniteTime P L.X hMeas hDet (T n) (hCount n) (hFib n)
    (hZero n) (fun w hw => (hT w hw).1 n)
  have hConv : ∀ B : Set Omega, MeasurableSet (B ∩ D) →
      ∀ᵐ w ∂P.restrict (B ∩ D), ∀ u : NNReal,
        Tendsto (fun n => Y n w u) atTop (nhds (Z w u)) := by
    intro B hB
    filter_upwards [ae_restrict_mem hB] with w hw u
    obtain ⟨hAbove, hlim⟩ := hT w hw.2
    exact Kyprianou.Ch04.exercise46RightGridFutureLimitV1 P F L finiteTime T w hAbove hlim u
  have hAll : ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w | tau w ≤ (s : WithTop NNReal)})) →
      AEMeasurable Z (P.restrict (B ∩ D)) ∧
      Measure.map Z (P.restrict (B ∩ D)) = P (B ∩ D) • nu := by
    intro B hB
    exact strongMarkovPathLawOfCommonAELimitsV1 (P.restrict (B ∩ D)) Y Z
      (P (B ∩ D) • nu) (fun n => (hGrid n).1)
      (fun n => (hGrid n).2 B hB)
      (hConv B (strongMarkovFiniteStoppedEventMeasV1 F tau hTau B hB))
  refine ⟨?_, fun B hB => (hAll B hB).2⟩
  simpa [D, Z] using (hAll Set.univ (fun s => by simpa using hTau s)).1

