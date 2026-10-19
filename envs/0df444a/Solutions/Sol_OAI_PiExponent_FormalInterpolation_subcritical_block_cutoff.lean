-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.subcritical_block_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:07:39.061403+00:00
-- url     : https://prove2.me/submissions/58140e8e-3105-46cd-b413-62cca71ad8f3

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (R : Real) (hR : 0 < R)
    (s : Nat) (hs : 0 < s)
    (D : Real) (hD : D < (s : Real) * R)
    (C : Real) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∃ k : Nat, k * s < n ∧ n ≤ (k + 1) * s ∧
        C + (k : Real) * max D 0 ≤ (n : Real) * R := by
  let A : Real := max D 0
  let δ : Real := (s : Real) * R - A
  have hsR : 0 < (s : Real) := Nat.cast_pos.mpr hs
  have hA0 : 0 ≤ A := le_max_right D 0
  have hAlt : A < (s : Real) * R := max_lt hD (mul_pos hsR hR)
  have hδ : 0 < δ := sub_pos.mpr hAlt
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C * (s : Real) / δ)
  have hN₀' : C * (s : Real) < (N₀ : Real) * δ :=
    (div_lt_iff₀ hδ).mp hN₀
  refine ⟨max N₀ 1, ?_⟩
  intro n hn
  have hN₀n : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := by omega
  let k : Nat := (n - 1) / s
  have hdecomp : (n - 1) % s + k * s = n - 1 := by
    dsimp [k]
    simpa only [Nat.mul_comm] using (Nat.mod_add_div (n - 1) s)
  have hr : (n - 1) % s < s := Nat.mod_lt _ hs
  have hks : k * s < n := by omega
  have hnblock : n ≤ (k + 1) * s := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hkR : (k : Real) * (s : Real) ≤ (n : Real) := by
    simpa only [Nat.cast_mul] using
      (Nat.cast_le.mpr (Nat.le_of_lt hks) : ((k * s : Nat) : Real) ≤ (n : Real))
  have hN₀R : (N₀ : Real) ≤ (n : Real) := Nat.cast_le.mpr hN₀n
  have hNδ : (N₀ : Real) * δ ≤ (n : Real) * δ :=
    mul_le_mul_of_nonneg_right hN₀R hδ.le
  have hCδ : C * (s : Real) ≤ (n : Real) * δ := le_trans hN₀'.le hNδ
  have hkA : ((k : Real) * (s : Real)) * A ≤ (n : Real) * A :=
    mul_le_mul_of_nonneg_right hkR hA0
  have hscaled : (s : Real) * (C + (k : Real) * A) ≤
      (s : Real) * ((n : Real) * R) := by
    dsimp [δ] at hCδ
    nlinarith only [hCδ, hkA]
  refine ⟨k, hks, hnblock, ?_⟩
  exact (mul_le_mul_iff_of_pos_left hsR).mp hscaled