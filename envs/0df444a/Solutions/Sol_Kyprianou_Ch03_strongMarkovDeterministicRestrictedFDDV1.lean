-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovDeterministicRestrictedFDDV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:18:03.174903+00:00
-- url     : https://prove2.me/submissions/95f9e715-ee8b-4053-86bb-d96bf8e4a0d9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovGridPositionLawV1
import Theorems.Thm_AvramDividend_Classical_finite_time_set_has_monotone_zero_started_grid
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C}) :
    ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      ∀ J : Finset NNReal,
        Measure.map (fun w : Omega => fun j : J =>
          X (s + (j : NNReal)) w - X s w) (P.restrict B) =
        P B • Measure.map (fun w : Omega => fun j : J => X (j : NNReal) w) P := by
  classical
  intro s B hB J
  obtain ⟨t, ht, ht0, n, henum⟩ :=
    AvramDividend.Classical.finite_time_set_has_monotone_zero_started_grid J
  let f : J → Fin n := fun j => Classical.choose (henum j)
  have hf (j : J) : t ((f j).val+1) = j.val := Classical.choose_spec (henum j)
  let proj : (Fin n → ℝ) → (J → ℝ) := fun v j => v (f j)
  have hp : Measurable proj := measurable_pi_iff.mpr (fun j => measurable_pi_apply (f j))
  have hm (u : NNReal) : Measurable (X u) := (hAdapt u).mono (F.le u) le_rfl
  let U : Omega → (Fin n → ℝ) := fun w i => X (s+t (i.val+1)) w - X s w
  let V : Omega → (Fin n → ℝ) := fun w i => X (t (i.val+1)) w
  have hU : Measurable U := measurable_pi_iff.mpr (fun i => (hm _).sub (hm _))
  have hV : Measurable V := measurable_pi_iff.mpr (fun i => hm _)
  have hGrid : Measure.map U (P.restrict B) = P B • Measure.map V P :=
    Kyprianou.Ch03.strongMarkovGridPositionLawV1 P F X hAdapt hOne hX s B hB t ht ht0 n
  have he := congrArg (Measure.map proj) hGrid
  rw [Measure.map_map hp hU, Measure.map_smul, Measure.map_map hp hV] at he
  simpa only [Function.comp_def, proj, U, V, hf] using he
