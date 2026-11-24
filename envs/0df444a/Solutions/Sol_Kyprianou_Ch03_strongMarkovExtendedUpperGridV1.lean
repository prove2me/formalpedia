-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovExtendedUpperGridV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:58:35.059097+00:00
-- url     : https://prove2.me/submissions/58e5ca07-9665-4b5b-a317-1286ab031b68

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicFiniteFibresV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDyadicRangeV1
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal)) :
    ∃ (T : ℕ → Omega → NNReal),
      (∀ n, Countable (Set.range (T n))) ∧
      (∀ n s, MeasurableSet[F s]
        ({w : Omega | tau w ≠ ⊤} ∩ {w | T n w = s})) ∧
      (∀ n w, tau w = ⊤ → T n w = 0) ∧
      (∀ w, tau w ≠ ⊤ → (∀ n, finiteTime w ≤ T n w) ∧
        Tendsto (fun n => T n w) atTop (nhds (finiteTime w))) := by
  classical
  let T : ℕ → Omega → NNReal := fun n w => if tau w = ⊤ then 0 else
    (Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) : NNReal) / (2 : NNReal)^n
  refine ⟨T, fun n => strongMarkovDyadicRangeV1 tau finiteTime n,
    fun n s => strongMarkovDyadicFiniteFibresV1 F tau hTau finiteTime hFiniteTime n s,
    fun n w hw => by simp [T, hw], ?_⟩
  intro w hw
  simp only [T, if_neg hw]
  exact ⟨AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal (finiteTime w),
    AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto (finiteTime w)⟩
