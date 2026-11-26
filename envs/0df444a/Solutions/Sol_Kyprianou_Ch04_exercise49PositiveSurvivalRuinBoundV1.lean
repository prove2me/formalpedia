-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PositiveSurvivalRuinBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:02:59.317949+00:00
-- url     : https://prove2.me/submissions/4f561b03-610f-41fd-a078-65331fea49b5

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49FutureSafeEventV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Positive survival mass implies strict upper bound on eventual ruin probability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (hS : 0 < P {ω | ∀ u : NNReal, 0 ≤ X u ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  let S : Set Ω := {ω | ∀ u : NNReal, 0 ≤ X u ω}
  obtain ⟨C, hCm, hCc⟩ := Kyprianou.Ch04.exercise49FutureSafeEventV1 0
  have hSm : MeasurableSet S := by
    have hEq : S = (fun (ω : Ω) u => X u ω) ⁻¹' C := by
      ext ω
      exact (hCc _ (hc ω)).symm
    rw [hEq]
    exact (measurable_pi_iff.mpr hm) hCm
  have hR : {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤} = Sᶜ := by
    ext ω
    change sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0} ≠ ⊤ ↔ ¬ ∀ u : NNReal, 0 ≤ X u ω
    constructor
    · intro h hSω
      obtain ⟨_, ⟨u, rfl, _, hu⟩, _⟩ := sInf_lt_iff.mp (lt_top_iff_ne_top.mpr h)
      exact (not_lt_of_ge (hSω u)) hu
    · intro h htop
      apply h
      intro u
      by_contra! hn
      have hu : 0 < u := by
        by_contra! hu
        have he : u = 0 := le_antisymm hu bot_le
        rw [he, congrFun hX.start_zero ω] at hn
        exact (lt_irrefl 0) hn
      have hle : (sInf {v : WithTop NNReal | ∃ t : NNReal,
          v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≤ ↑u :=
        sInf_le ⟨u, rfl, hu, hn⟩
      rw [htop] at hle
      exact WithTop.coe_ne_top (top_le_iff.mp hle)
  rw [hR]
  have htotal := measure_add_measure_compl (μ := P) hSm
  have hsum : (P S).toReal + (P Sᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _), htotal]
    simp
  have hpos : 0 < (P S).toReal := ENNReal.toReal_pos hS.ne' (measure_ne_top P _)
  linarith
