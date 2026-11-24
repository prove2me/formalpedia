-- Prove2me | solution 2 for Kyprianou.Ch03.strongMarkovCountableGridRestrictedLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:07:53.308699+00:00
-- url     : https://prove2.me/submissions/fbed9ee9-f9ed-4961-a335-f111dad0196e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableFibreMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableFibreFactorV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
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
  classical
  let D : Set Omega := {w | tau w ≠ ⊤}
  let Y : NNReal → Omega → (NNReal → ℝ) := fun s w u => X (s+u) w - X s w
  have hD : MeasurableSet D := by
    simpa [D] using strongMarkovFiniteStoppedEventMeasV1 F tau hTau Set.univ
      (fun s => by simpa using hTau s)
  have hY (s : NNReal) : Measurable (Y s) :=
    measurable_pi_iff.mpr (fun u => (hMeas (s+u)).sub (hMeas s))
  have hF (s : NNReal) : MeasurableSet {w | T w = s} := by
    have hf := F.le s _ (hFib s)
    by_cases hs : s = 0
    · subst s
      convert hf.union hD.compl using 1
      ext w
      by_cases hw : tau w = ⊤
      · simp [D, hw, hZero w hw]
      · simp [D, hw]
    · convert hf using 1
      ext w
      by_cases hw : tau w = ⊤
      · simp [D, hw, hZero w hw, Ne.symm hs]
      · simp [D, hw]
  have hz := strongMarkovCountableFibreMeasurableV1 T hCount hF Y hY
  refine ⟨hz, ?_⟩
  intro B hB
  have hBD := strongMarkovFiniteStoppedEventMeasV1 F tau hTau B hB
  have hb (s : NNReal) : MeasurableSet[F s] ((B ∩ D) ∩ {w | T w = s}) := by
    convert (hB s).inter (hFib s) using 1
    ext w
    change (w ∈ B ∧ tau w ≠ ⊤) ∧ T w = s ↔
      (w ∈ B ∧ tau w ≤ (s : WithTop NNReal)) ∧ (tau w ≠ ⊤ ∧ T w = s)
    constructor
    · rintro ⟨⟨hw, hd⟩, ht⟩
      refine ⟨⟨hw, ?_⟩, hd, ht⟩
      rw [hFiniteTime w hd, WithTop.coe_le_coe, ← ht]
      exact hAbove w hd
    · rintro ⟨⟨hw, _⟩, hd, ht⟩
      exact ⟨⟨hw, hd⟩, ht⟩
  exact strongMarkovCountableFibreFactorV1 P (B ∩ D) hBD T hCount Y
    (fun w => Y (T w) w) (Measure.map (fun w u => X u w) P)
    hz (fun _ => rfl) (fun s => F.le s _ (hb s)) (fun s => hDet s _ (hb s))
