-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.zeroDimensional_weightedSimplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:48:27.454581+00:00
-- url     : https://prove2.me/submissions/418edcb6-1743-4dd8-924a-08ba9bf3f6ca

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution
    (w : Fin 0 → Real) (hw : ∀ i, 0 < w i) (H : Real) (hH : 0 ≤ H) :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
          (∑ i, w i * x i) ≤ H + Finset.univ.sum w} =
      ENNReal.ofReal
        ((H + Finset.univ.sum w) ^ 0 /
          ((Nat.factorial 0 : Real) * Finset.univ.prod w)) := by
  classical
  have hset :
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
        (∑ i, w i * x i) ≤ H + Finset.univ.sum w} = Set.univ := by
    ext x
    simp [hH]
  have hbox : (Set.univ : Set (Fin 0 → Real)) =
      Set.Icc (fun _ : Fin 0 => (0 : Real)) (fun _ => 0) := by
    ext x
    have hx : x = (fun _ : Fin 0 => (0 : Real)) := by
      funext i
      exact Fin.elim0 i
    rw [hx]
    simp [Set.mem_Icc]
  rw [hset, hbox, Real.volume_Icc_pi]
  simp