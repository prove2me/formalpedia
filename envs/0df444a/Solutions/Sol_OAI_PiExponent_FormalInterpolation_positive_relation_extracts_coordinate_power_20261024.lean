-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.positive_relation_extracts_coordinate_power_20261024
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:40:03.449128+00:00
-- url     : https://prove2.me/submissions/da139717-eed5-4552-8407-1d60ffaac576

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → Rat)
    (hw : ∀ j, 0 < (w j : Real))
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (hcomp : ∀ p ∈ I, ∀ r : Rat,
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) r p ∈ I)
    (i : Fin d) (N : Nat) (c : Fin (N + 1) → Complex)
    (hpos : ∃ k : Fin (N + 1), k.val ≠ 0 ∧ c k ≠ 0)
    (hmem : (∑ k : Fin (N + 1),
      MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I) :
    ∃ n : Nat, 0 < n ∧ MvPolynomial.X i ^ n ∈ I := by
  classical
  obtain ⟨k, hkpos, hck⟩ := hpos
  let W : Fin d → Rat := fun j => w j
  let deg : Fin (N + 1) → Rat := fun j => (j.val : Rat) * w i
  have hwi : w i ≠ 0 := by
    have hposRat : 0 < w i := by exact_mod_cast hw i
    exact ne_of_gt hposRat
  have hhom (j : Fin (N + 1)) :
      MvPolynomial.IsWeightedHomogeneous W
        (MvPolynomial.X i ^ (j : Nat) : MvPolynomial (Fin d) Complex) (deg j) := by
    dsimp [W, deg]
    have hx : MvPolynomial.IsWeightedHomogeneous
        (fun x : Fin d => (w x : Rat))
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) (w i) := by
      exact MvPolynomial.isWeightedHomogeneous_X
        (R := Complex) (σ := Fin d) (fun x : Fin d => (w x : Rat)) i
    have hp := hx.pow (j : Nat)
    simpa using hp
  have hdegree (j : Fin (N + 1)) (hjk : j ≠ k) : deg j ≠ deg k := by
    intro heq
    have hcast : (j.val : Rat) = (k.val : Rat) := by
      apply mul_right_cancel₀ hwi
      exact heq
    have hv : j.val = k.val := by exact_mod_cast hcast
    exact hjk (Fin.ext hv)
  have hproj :
      MvPolynomial.weightedHomogeneousComponent W (deg k)
        (∑ j : Fin (N + 1), MvPolynomial.C (c j) * MvPolynomial.X i ^ (j : Nat)) =
        MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat) := by
    rw [map_sum, Finset.sum_eq_single k]
    · rw [MvPolynomial.weightedHomogeneousComponent_C_mul]
      rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (hhom k)]
    · intro j hj hjk
      rw [MvPolynomial.weightedHomogeneousComponent_C_mul]
      rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne
        (deg k) (hhom j) (Ne.symm (hdegree j hjk))]
      simp
    · intro hk
      exact (hk (Finset.mem_univ k)).elim
  have hterm : MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat) ∈ I := by
    have hcomponent := hcomp _ hmem (deg k)
    simpa [hproj, W] using hcomponent
  refine ⟨k.val, Nat.pos_of_ne_zero hkpos, ?_⟩
  have hmul : MvPolynomial.C ((c k)⁻¹) *
      (MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) ∈ I :=
    I.mul_mem_left _ hterm
  have hcancel : MvPolynomial.C ((c k)⁻¹) *
      (MvPolynomial.C (c k) * MvPolynomial.X i ^ (k : Nat)) =
      MvPolynomial.X i ^ (k : Nat) := by
    rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hck,
      MvPolynomial.C_1, one_mul]
  simpa [hcancel] using hmul