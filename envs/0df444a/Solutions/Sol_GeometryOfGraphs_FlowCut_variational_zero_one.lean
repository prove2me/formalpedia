-- Prove2me | solution 1 for GeometryOfGraphs.FlowCut.variational_zero_one
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:46:58.987146+00:00
-- url     : https://prove2.me/submissions/dbf7f71c-973a-4bd2-a308-2610192d9db3

import Mathlib

set_option autoImplicit false

namespace Cex816a

def a (i j : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then -1 else 0

def b (i j : Fin 3) : ℝ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0

def z (i : Fin 3) : ℝ := (i.val : ℝ)

theorem hb (i j : Fin 3) : 0 ≤ b i j := by
  fin_cases i <;> fin_cases j <;> simp [b]

theorem ha_symm (i j : Fin 3) : a i j = a j i := by
  fin_cases i <;> fin_cases j <;> simp [a]

theorem hb_symm (i j : Fin 3) : b i j = b j i := by
  fin_cases i <;> fin_cases j <;> simp [b]

theorem hz : 0 < ∑ i : Fin 3, ∑ j : Fin 3, b i j * |z i - z j| := by
  simp [Fin.sum_univ_three, b, z]

theorem no_S (S : Finset (Fin 3)) :
    ¬ (0 < ∑ i : Fin 3, ∑ j : Fin 3, b i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)| ∧
      (∑ i : Fin 3, ∑ j : Fin 3, a i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) *
          (∑ i : Fin 3, ∑ j : Fin 3, b i j * |z i - z j|) ≤
        (∑ i : Fin 3, ∑ j : Fin 3, a i j * |z i - z j|) *
          (∑ i : Fin 3, ∑ j : Fin 3, b i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|)) := by
  by_cases h0 : (0 : Fin 3) ∈ S <;>
    by_cases h1 : (1 : Fin 3) ∈ S <;>
    by_cases h2 : (2 : Fin 3) ∈ S <;>
    simp [Fin.sum_univ_three, a, b, z, h0, h1, h2] <;>
    norm_num

end Cex816a

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (a b : V → V → ℝ)
    (_hb : ∀ i j, 0 ≤ b i j)
    (_ha_symm : ∀ i j, a i j = a j i) (_hb_symm : ∀ i j, b i j = b j i)
    (z : V → ℝ) (_hz : 0 < ∑ i, ∑ j, b i j * |z i - z j|),
    ∃ S : Finset V,
      0 < ∑ i, ∑ j, b i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)| ∧
      (∑ i, ∑ j, a i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) *
          (∑ i, ∑ j, b i j * |z i - z j|) ≤
        (∑ i, ∑ j, a i j * |z i - z j|) *
          (∑ i, ∑ j, b i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|)) := by
  intro hall
  obtain ⟨S, hS⟩ := hall Cex816a.a Cex816a.b Cex816a.hb Cex816a.ha_symm Cex816a.hb_symm Cex816a.z Cex816a.hz
  exact Cex816a.no_S S hS
