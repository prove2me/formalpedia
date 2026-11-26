-- Prove2me | solution 1 for Kyprianou.Ch04.frozenPathMarkedCountV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:16:26.557818+00:00
-- url     : https://prove2.me/submissions/5cf4c246-5f26-4440-bd99-1bb631390acf

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Restricting to past time-mark cells, deterministic freezing preserves the jump set. -/
theorem solution (Y L : NNReal → ℝ) (T : NNReal)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u)))
    (D : Set (ℝ × ℝ)) (hD : D ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ univ) :
    let Z := fun v : NNReal => Y (min v T)
    {u : NNReal | 0 < u ∧ Y u ≠ L u ∧ ((u : ℝ), Y u - L u) ∈ D} =
      {u : NNReal | 0 < u ∧ Z u - Function.leftLim Z u ≠ 0 ∧
        ((u : ℝ), Z u - Function.leftLim Z u) ∈ D} := by
  intro Z
  ext u
  by_cases hp : 0 < u
  · by_cases hu : u ≤ T
    · haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0,hp⟩
      have hZu : Z u = Y u := by simp [Z,min_eq_left hu]
      have hZL : Function.leftLim Z u = L u :=
        leftLim_eq_of_tendsto (Kyprianou.Ch04.frozenPathLeftLimitV1 Y T u (L u) hu (hL u hp))
      simp [hp,hZu,hZL,sub_ne_zero]
    · have hnot (z : ℝ) : ((u : ℝ), z) ∉ D := by
        intro hz
        exact hu (by exact_mod_cast (hD hz).1.2)
      simp [hnot]
  · simp [hp]
