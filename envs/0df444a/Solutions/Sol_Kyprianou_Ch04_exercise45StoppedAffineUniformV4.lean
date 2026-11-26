-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedAffineUniformV4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:38:32.538799+00:00
-- url     : https://prove2.me/submissions/076f01c9-f431-4117-99d3-1c5db83adc68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedAffineGridDecompV4
import Theorems.Thm_Kyprianou_Ch04_exercise45UniformWeightedErrorV4
import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedDriftUniformErrorV4
import Theorems.Thm_Kyprianou_Ch04_exercise45StoppedSingleAtomErrorV4
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (T : NNReal) (S : Finset NNReal) (a H Y : NNReal → ℝ) (b C : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then a r else 0)
    (hH : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r)))
    (hb : ∀ r, |H r| ≤ C) :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |(∑ i ∈ Finset.range (n+1),
        let u := T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
        let v := T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)
        H u * (Y (min t v) - Y (min t u))) -
        (b * (∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) +
          ∑ r ∈ S, if r ≤ t then a r * H r else 0)| < δ := by
  let u (n i : ℕ) := T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
  let D (n : ℕ) (t : NNReal) := ∑ i ∈ Finset.range (n+1),
    H (u n i) * ((min t (u n (i+1)) : NNReal).toReal - (min t (u n i) : NNReal).toReal)
  let J (r : NNReal) (n : ℕ) (t : NNReal) := ∑ i ∈ Finset.range (n+1),
    if min t (u n i) < r ∧ r ≤ min t (u n (i+1)) then H (u n i) else 0
  have hD := Kyprianou.Ch04.exercise45StoppedDriftUniformErrorV4 T H C hb hH
  have hJ (r : NNReal) (hr : r ∈ S) (δ : ℝ) (hd : 0 < δ) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |J r n t - (if r ≤ t then H r else 0)| < δ := by
    obtain ⟨N,hN⟩ := Kyprianou.Ch04.exercise45StoppedSingleAtomErrorV4 T r
      (hS r hr).1 (hS r hr).2 H (hH r (hS r hr).1) δ hd
    exact ⟨N,fun n hn t _ => hN n hn t⟩
  intro δ hd
  obtain ⟨N,hN⟩ := Kyprianou.Ch04.exercise45UniformWeightedErrorV4 S T D
    (fun t => ∫ s in Icc (0 : ℝ) (t : ℝ), H s.toNNReal) J
    (fun r t => if r ≤ t then H r else 0) b a hD hJ δ hd
  refine ⟨N,fun n hn t ht => ?_⟩
  rw [Kyprianou.Ch04.exercise45StoppedAffineGridDecompV4 T t ht n S a H Y b hY]
  have hEq : (∑ r ∈ S, a r * (if r ≤ t then H r else 0)) =
      ∑ r ∈ S, if r ≤ t then a r * H r else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    split <;> simp_all
  simpa only [D,J,u,hEq] using hN n hn t ht