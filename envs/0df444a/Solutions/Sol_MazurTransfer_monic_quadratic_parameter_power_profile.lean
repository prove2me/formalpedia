-- Prove2me | solution 1 for MazurTransfer.monic_quadratic_parameter_power_profile
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-15T04:46:46.315047+00:00
-- url     : https://prove2.me/submissions/6325a978-1ec7-4a08-8ef6-0cf83571df99

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: monic polynomial recurrence for powers of a translated
mixed quadratic root. Named downstream consumer: mixed single-section
finite-algebra bases over the dyadic integral coefficient ring.
-/
import Mathlib
noncomputable section
namespace MazurTransfer.MonicQuadraticParameterPowerProfileProof
open Polynomial
variable (R : Type*) [CommRing R] [IsDomain R] (h f : Polynomial R)

def coefficients : ℕ → Polynomial R × Polynomial R :=
  Nat.rec (1, 0) (fun _ v => (h * v.1 + f * v.2, v.1))

omit [IsDomain R] in
theorem coefficients_succ (n : ℕ) : coefficients R h f (n + 1) =
    (h * (coefficients R h f n).1 + f * (coefficients R h f n).2, (coefficients R h f n).1) := rfl

theorem profile (hh : h.Monic) (hdeg : f.natDegree < h.natDegree) (n : ℕ) :
    (coefficients R h f n).1.Monic ∧
    (coefficients R h f n).1.natDegree = h.natDegree * n ∧
    (coefficients R h f n).2.natDegree ≤ h.natDegree * n := by
  induction n with
  | zero => exact ⟨monic_one, by simp [coefficients], by simp [coefficients]⟩
  | succ n ih =>
    rcases ih with ⟨hm,hd,hb⟩
    have hmA := hh.mul hm
    have hdA : (h * (coefficients R h f n).1).natDegree = h.natDegree * n + h.natDegree := by
      rw [hh.natDegree_mul' hm.ne_zero, hd]
      omega
    have hdB : (f * (coefficients R h f n).2).natDegree ≤ h.natDegree * n + f.natDegree := by
      have ht := natDegree_mul_le (p := f) (q := (coefficients R h f n).2)
      omega
    have hlt : (f * (coefficients R h f n).2).natDegree <
        (h * (coefficients R h f n).1).natDegree := by omega
    have hmon := hmA.add_of_left (degree_lt_degree hlt)
    have hde := natDegree_add_eq_left_of_natDegree_lt hlt
    simp only [coefficients_succ]
    exact ⟨hmon, by rw [hde,hdA,Nat.mul_succ], by rw [hd,Nat.mul_succ]; omega⟩
end MazurTransfer.MonicQuadraticParameterPowerProfileProof

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] (h f : Polynomial R)
    (hh : h.Monic) (hdeg : f.natDegree < h.natDegree) (n : ℕ) :
    let c : ℕ → Polynomial R × Polynomial R :=
      Nat.rec (1, 0) (fun _ v => (h * v.1 + f * v.2, v.1))
    (c n).1.Monic ∧ (c n).1.natDegree = h.natDegree * n ∧
      (c n).2.natDegree ≤ h.natDegree * n  := by
  change (MazurTransfer.MonicQuadraticParameterPowerProfileProof.coefficients R h f n).1.Monic ∧
    (MazurTransfer.MonicQuadraticParameterPowerProfileProof.coefficients R h f n).1.natDegree = h.natDegree * n ∧
    (MazurTransfer.MonicQuadraticParameterPowerProfileProof.coefficients R h f n).2.natDegree ≤ h.natDegree * n
  exact MazurTransfer.MonicQuadraticParameterPowerProfileProof.profile R h f hh hdeg n
#print axioms solution
