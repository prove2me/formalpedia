-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_mul_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:30:59.030273+00:00
-- url     : https://prove2.me/submissions/af6f0ef5-3d80-480e-9b9e-c8cdc4d7a95c

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem solution
    {d : Nat} (w : Fin d -> Rat) (D E : Real)
    (a g : MvPolynomial (Fin d) Complex)
    (hg : g.IsWeightedHomogeneous (fun i => (w i : Real)) D) :
    MvPolynomial.weightedHomogeneousComponent (fun i => (w i : Real)) E (a * g) =
      MvPolynomial.weightedHomogeneousComponent (fun i => (w i : Real)) (E - D) a * g := by
  classical
  apply MvPolynomial.ext
  intro c
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul]
  by_cases hc : Finsupp.weight (fun i : Fin d => (w i : Real)) c = E
  · simp only [if_pos hc]
    apply Finset.sum_congr rfl
    intro x hx
    rcases x with ⟨u, v⟩
    have huv : u + v = c := Finset.mem_antidiagonal.mp hx
    by_cases hv : MvPolynomial.coeff v g = 0
    · simp [hv]
    · have hD : Finsupp.weight (fun i : Fin d => (w i : Real)) v = D := hg hv
      have hwt : Finsupp.weight (fun i : Fin d => (w i : Real)) c =
          Finsupp.weight (fun i : Fin d => (w i : Real)) u + D := by
        calc
          Finsupp.weight (fun i : Fin d => (w i : Real)) c =
              Finsupp.weight (fun i : Fin d => (w i : Real)) (u + v) :=
            congrArg (Finsupp.weight (fun i : Fin d => (w i : Real))) huv.symm
          _ = Finsupp.weight (fun i : Fin d => (w i : Real)) u +
              Finsupp.weight (fun i : Fin d => (w i : Real)) v := map_add _ _ _
          _ = Finsupp.weight (fun i : Fin d => (w i : Real)) u + D := by rw [hD]
      have hiff : (Finsupp.weight (fun i : Fin d => (w i : Real)) c = E) ↔
          (Finsupp.weight (fun i : Fin d => (w i : Real)) u = E - D) := by
        rw [hwt]
        constructor <;> intro h <;> linarith
      have huE : Finsupp.weight (fun i : Fin d => (w i : Real)) u = E - D :=
        hiff.mp hc
      simp [huE]
  · simp only [if_neg hc]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rcases x with ⟨u, v⟩
    have huv : u + v = c := Finset.mem_antidiagonal.mp hx
    by_cases hv : MvPolynomial.coeff v g = 0
    · simp [hv]
    · have hD : Finsupp.weight (fun i : Fin d => (w i : Real)) v = D := hg hv
      have hwt : Finsupp.weight (fun i : Fin d => (w i : Real)) c =
          Finsupp.weight (fun i : Fin d => (w i : Real)) u + D := by
        calc
          Finsupp.weight (fun i : Fin d => (w i : Real)) c =
              Finsupp.weight (fun i : Fin d => (w i : Real)) (u + v) :=
            congrArg (Finsupp.weight (fun i : Fin d => (w i : Real))) huv.symm
          _ = Finsupp.weight (fun i : Fin d => (w i : Real)) u +
              Finsupp.weight (fun i : Fin d => (w i : Real)) v := map_add _ _ _
          _ = Finsupp.weight (fun i : Fin d => (w i : Real)) u + D := by rw [hD]
      have hu : Finsupp.weight (fun i : Fin d => (w i : Real)) u ≠ E - D := by
        intro hu
        apply hc
        rw [hwt]
        linarith
      simp [hu]