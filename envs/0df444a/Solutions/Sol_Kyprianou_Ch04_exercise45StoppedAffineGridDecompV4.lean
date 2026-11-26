-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StoppedAffineGridDecompV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:19:25.960635+00:00
-- url     : https://prove2.me/submissions/f281e65d-3473-4dd0-bf0c-0ea8062f8422

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteJumpGridSumDecompositionV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (T t : NNReal) (ht : t ≤ T) (n : ℕ) (S : Finset NNReal)
    (a H Y : NNReal → ℝ) (b : ℝ)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then a r else 0) :
    let u : ℕ → NNReal := fun i => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
    (∑ i ∈ Finset.range (n+1), H (u i) * (Y (min t (u (i+1))) - Y (min t (u i)))) =
      b * (∑ i ∈ Finset.range (n+1), H (u i) *
        ((min t (u (i+1)) : NNReal).toReal - (min t (u i) : NNReal).toReal)) +
      ∑ r ∈ S, a r * (∑ i ∈ Finset.range (n+1),
        if min t (u i) < r ∧ r ≤ min t (u (i+1)) then H (u i) else 0) := by
  intro u
  let V := fun s : ℝ => b*s + ∑ r ∈ S, if (r : ℝ) ≤ s then a r else 0
  have hv (s : NNReal) (hs : s ≤ T) : Y s = V s := by
    rw [hY s hs]
    simp [V,NNReal.coe_le_coe]
  have hm (i : ℕ) : min t (u i) ≤ min t (u (i+1)) := by
    apply min_le_min le_rfl
    dsimp [u]
    gcongr <;> omega
  have h := Kyprianou.Ch04.finiteJumpGridSumDecompositionV1 S (n+1)
    (fun i => (min t (u i) : ℝ)) (fun i => (min t (u (i+1)) : ℝ))
    (fun i => H (u i)) (fun r => (r : ℝ)) a b V (fun _ => rfl)
    (fun i _ => by exact_mod_cast hm i)
  have hEq (i : ℕ) : Y (min t (u i)) = V (min t (u i) : ℝ) :=
    hv _ ((min_le_left _ _).trans ht)
  simp_rw [hEq]
  simpa only [NNReal.coe_min,NNReal.coe_lt_coe,NNReal.coe_le_coe] using! h
