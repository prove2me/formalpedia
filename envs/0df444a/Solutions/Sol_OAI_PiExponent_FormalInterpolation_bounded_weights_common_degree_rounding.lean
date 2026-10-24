-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:48:52.161557+00:00
-- url     : https://prove2.me/submissions/9ef268d3-e011-48f0-87a4-a0924f12cfca

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i : Fin d, 0 < (w i : Real))
    (B : Nat) (L : Nat) (hL : 0 < L) (c : Fin d → Nat)
    (hc : ∀ i : Fin d, 0 < c i ∧ (c i : Real) * (w i : Real) = (L : Real))
    (n : Fin d → Nat)
    (hn : ∀ i : Fin d, 0 < n i ∧ (n i : Real) * (w i : Real) ≤ (B : Real))
    (Q : Nat) :
    ∃ q : Nat, ∃ D : Nat, 0 < q ∧ Q ≤ q ∧ 0 < D ∧
      (D : Real) ≤ ((q * B + L : Nat) : Real) ∧
      ∀ i : Fin d, ∃ m : Nat,
        q * n i ≤ m ∧ 0 < m ∧ (m : Real) * (w i : Real) = (D : Real) := by
  let q : Nat := max Q 1
  have hqpos : 0 < q := by
    dsimp [q]
    omega
  have hQ : Q ≤ q := by
    dsimp [q]
    exact Nat.le_max_left _ _
  let x : Nat := q * B / L
  let r : Nat := q * B % L
  let D : Nat := L * (x + 1)
  have hr : r < L := by
    dsimp [r]
    exact Nat.mod_lt _ hL
  have hdecomp : r + L * x = q * B := by
    dsimp [r, x]
    simpa [Nat.mul_comm] using Nat.mod_add_div (q * B) L
  have hDval : D = L * x + L := by
    dsimp [D]
    rw [Nat.mul_add]
    simp
  have hqB_le_D : q * B ≤ D := by
    omega
  have hD_le : D ≤ q * B + L := by
    omega
  have hDpos : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos hL (Nat.succ_pos _)
  have hqB_le_D_real : (q * B : Nat) ≤ D := hqB_le_D
  refine ⟨q, D, hqpos, hQ, hDpos, ?_, ?_⟩
  · exact_mod_cast hD_le
  · intro i
    let m : Nat := c i * (x + 1)
    have hmpos : 0 < m := by
      dsimp [m]
      exact Nat.mul_pos (hc i).1 (Nat.succ_pos _)
    have hmweight : (m : Real) * (w i : Real) = (D : Real) := by
      dsimp [m, D]
      calc
        ((c i * (x + 1) : Nat) : Real) * (w i : Real)
            = ((x + 1 : Nat) : Real) * ((c i : Real) * (w i : Real)) := by
                push_cast
                ring
        _ = ((x + 1 : Nat) : Real) * (L : Real) := by rw [(hc i).2]
        _ = ((L * (x + 1) : Nat) : Real) := by
              push_cast
              ring
    have hscaled : ((q * n i : Nat) : Real) * (w i : Real) ≤ (q * B : Nat) := by
      have hmul := mul_le_mul_of_nonneg_left (hn i).2 (show 0 ≤ (q : Real) by positivity)
      calc
        ((q * n i : Nat) : Real) * (w i : Real)
            = (q : Real) * ((n i : Real) * (w i : Real)) := by
                push_cast
                ring
        _ ≤ (q : Real) * (B : Real) := hmul
        _ = ((q * B : Nat) : Real) := by push_cast; ring
    have hnat : q * n i ≤ m := by
      by_contra hnot
      have hgt : m < q * n i := Nat.lt_of_not_ge hnot
      have hgtR : (m : Real) < ((q * n i : Nat) : Real) := by exact_mod_cast hgt
      have hstrict := mul_lt_mul_of_pos_right hgtR (hw i)
      have hupper : ((q * n i : Nat) : Real) * (w i : Real) ≤ (D : Real) := by
        exact le_trans hscaled (by exact_mod_cast hqB_le_D)
      rw [hmweight] at hstrict
      linarith
    exact ⟨m, hnat, hmpos, hmweight⟩