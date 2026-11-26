-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45DyadicDominatedUCPV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:20:49.545936+00:00
-- url     : https://prove2.me/submissions/3d657608-9530-4834-baf5-b6a1450fab7f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45EventuallyAbsentEventsV5
import Theorems.Thm_Kyprianou_Ch04_exercise45StrictDyadicCrossingV5
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A countable measurable dyadic envelope transfers uniform a.e. convergence. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U V : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hm : ∀ n t, AEMeasurable (V n t) P)
    (hr : ∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => V n s w) (Ici t) t)
    (hb : ∀ᵐ w ∂P, ∀ n t, t ≤ T → |U n t w| ≤ |V n t w|)
    (hu : ∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |V n t w| < δ)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤ |U n t w|}).toReal) atTop (nhds 0) := by
  classical
  let q (j : ℕ) (k : Fin (2^j+1)) : NNReal := (k.val : NNReal) / (2 : NNReal)^j * T
  let Z (n j : ℕ) (k : Fin (2^j+1)) := (hm n (q j k)).mk (V n (q j k))
  let A (n : ℕ) := ⋃ j : ℕ, ⋃ k : Fin (2^j+1), {w | δ/2 < |Z n j k w|}
  have hZ : ∀ᵐ w ∂P, ∀ n j, ∀ k, Z n j k w = V n (q j k) w := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact (hm n (q j k)).ae_eq_mk.symm
  have hq := (Kyprianou.Ch04.exercise45StrictDyadicCrossingV5
    (fun _ => 0) T (fun _ => continuousWithinAt_const) (δ/2)).1
  have hA (n : ℕ) : MeasurableSet (A n) := by
    apply MeasurableSet.iUnion
    intro j
    apply MeasurableSet.iUnion
    intro k
    exact measurableSet_lt measurable_const ((hm n (q j k)).measurable_mk.abs)
  apply Kyprianou.Ch04.exercise45EventuallyAbsentEventsV5 P A _ hA
  · filter_upwards [hZ,hu] with w hwz hwu
    obtain ⟨N,hN⟩ := hwu (δ/2) (by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [A,mem_iUnion,mem_setOf_eq,not_exists]
    intro j k
    rw [hwz n j k]
    exact not_lt.mpr (hN n hn (q j k) (hq j k)).le
  · intro n
    filter_upwards [hZ,hr,hb] with w hwz hwr hwb
    rintro ⟨t,ht,hd⟩
    have hv : δ/2 < |V n t w| := by linarith [hwb n t ht]
    obtain ⟨j,k,hk⟩ := (Kyprianou.Ch04.exercise45StrictDyadicCrossingV5
      (fun s => V n s w) T (hwr n) (δ/2)).2.mp ⟨t,ht,hv⟩
    refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨k,?_⟩⟩
    change δ/2 < |Z n j k w|
    rw [hwz n j k]
    exact hk
