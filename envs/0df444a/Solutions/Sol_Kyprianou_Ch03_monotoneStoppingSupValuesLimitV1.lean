-- Prove2me | solution 1 for Kyprianou.Ch03.monotoneStoppingSupValuesLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:49:05.142055+00:00
-- url     : https://prove2.me/submissions/ab48158b-e057-4aac-b0f8-3aa23e876b6c

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_quasiLeftContinuousAlongStoppingTimes
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (T : ℕ → Omega → WithTop NNReal)
    (hStop : ∀ n, IsStoppingTime F (T n))
    (hMono : ∀ w, Monotone (fun n => T n w)) :
    ∀ᵐ w ∂P, (⨆ n, T n w) ≠ ⊤ →
      Tendsto (fun n => X ((T n w).untopD 0) w) atTop
        (𝓝 (X ((⨆ n, T n w).untopD 0) w)) := by
  let S (w : Omega) : WithTop NNReal := ⨆ n, T n w
  have hS : IsStoppingTime F S := by
    intro t
    have he : {w | S w ≤ (t : WithTop NNReal)} =
        ⋂ n, {w | T n w ≤ (t : WithTop NNReal)} := by
      ext w
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter, iSup_le_iff]
    rw [he]
    exact MeasurableSet.iInter fun n => hStop n t
  have hcoe (v : WithTop NNReal) (hv : v ≠ ⊤) : v = ((v.untopD 0 : NNReal) : WithTop NNReal) := by
    induction v using WithTop.recTopCoe with
    | top => exact (hv rfl).elim
    | coe v => rfl
  have h := (Kyprianou.Ch03.quasiLeftContinuousAlongStoppingTimes P F X hX hNatural
    S T (fun w => (S w).untopD 0) (fun n w => (T n w).untopD 0)
    (fun w hw => hcoe _ (by simpa using hw))
    (fun n w hw => hcoe _ (by simpa using hw)) hS hStop
    (Filter.Eventually.of_forall hMono)
    (Filter.Eventually.of_forall fun w => tendsto_atTop_iSup (hMono w))).1
  filter_upwards [h] with w hw
  intro hn
  exact hw (by simpa using hn)
