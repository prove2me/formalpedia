-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCountableGridRestrictedLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:06:35.157235+00:00
-- url     : https://prove2.me/submissions/d14a6650-6ccf-4430-be0b-e8926abcefc0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridMeasV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableGridSumLawV1
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false



theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hMeas : ∀ t, Measurable (X t))
    (hDet : ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s + u) w - X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (T : Omega → NNReal) (hCount : Countable (Set.range T))
    (hFib : ∀ s, MeasurableSet[F s]
      ({w : Omega | tau w ≠ ⊤} ∩ {w | T w = s}))
    (hZero : ∀ w, tau w = ⊤ → T w = 0)
    (hAbove : ∀ w, tau w ≠ ⊤ → finiteTime w ≤ T w) :
    Measurable (fun w : Omega => fun u : NNReal => X (T w + u) w - X (T w) w) ∧
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)})) →
      Measure.map (fun w => fun u : NNReal => X (T w + u) w - X (T w) w)
        (P.restrict (B ∩ {w : Omega | tau w ≠ ⊤})) =
      P (B ∩ {w : Omega | tau w ≠ ⊤}) • Measure.map (fun w u => X u w) P := by
  have hm := strongMarkovCountableGridMeasV1 F tau hTau X hMeas T hCount hFib hZero
  exact ⟨hm, strongMarkovCountableGridSumLawV1 P F tau finiteTime hFiniteTime
    X hMeas hDet T hCount hFib hAbove hm⟩
