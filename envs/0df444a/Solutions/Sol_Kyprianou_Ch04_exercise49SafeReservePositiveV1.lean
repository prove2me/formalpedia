-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49SafeReservePositiveV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:49:54.972403+00:00
-- url     : https://prove2.me/submissions/bddd98fa-c9ec-4321-a232-d3adbeaa087b

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A Levy process drifting to infinity has a finite safe reserve with positive probability. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hInf : ∀ᵐ ω ∂P, Tendsto (fun t => X t ω) atTop atTop) :
    ∃ n : ℕ, 0 < P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω} := by
  classical
  let A (n : ℕ) : Set Ω := {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω}
  have hA : ∀ᵐ ω ∂P, ω ∈ ⋃ n, A n := by
    filter_upwards [hInf, hX.cadlag_ae] with ω hi hc
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hi.eventually (eventually_ge_atTop (0 : ℝ)))
    obtain ⟨b, hb⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1
      (fun t => X t ω) hc (-1) T
    obtain ⟨n, hn⟩ := exists_nat_gt (max b 0)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    intro t
    by_cases ht : t ≤ T
    · have hbt : (-1 : ℝ) * X t ω ≤ b :=
        hb ⟨t, ⟨bot_le, ht⟩, rfl⟩
      have hbn := (le_max_left b 0).trans hn.le
      linarith
    · have hpos := hT t (le_of_not_ge ht)
      linarith [Nat.cast_nonneg (α := ℝ) n]
  by_contra! h
  have hz : P (⋃ n, A n) = 0 :=
    measure_iUnion_null (fun n => nonpos_iff_eq_zero.mp (h n))
  have hc : P (⋃ n, A n)ᶜ = 0 := (ae_iff.mp hA)
  have hu : P (Set.univ : Set Ω) = 0 := by
    rw [← Set.union_compl_self (⋃ n, A n)]
    exact le_antisymm ((measure_union_le _ _).trans (by rw [hz, hc, zero_add])) bot_le
  simpa using hu
