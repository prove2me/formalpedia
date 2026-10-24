-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.gaussian_int_det
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:36:01.651317+00:00
-- url     : https://prove2.me/submissions/7e534f0e-77ed-4d57-a80e-842d0b0609c7

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

open scoped BigOperators

theorem solution
    {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α Complex)
    (hA : ∀ i j, ∃ a b : Int, A i j = (a : Complex) + Complex.I * (b : Complex)) :
    ∃ a b : Int, A.det = (a : Complex) + Complex.I * (b : Complex) := by
  classical
  have hentry_exists (i j : α) : ∃ z : GaussianInt, GaussianInt.toComplex z = A i j := by
    rcases hA i j with ⟨a, b, hab⟩
    refine ⟨⟨a, b⟩, ?_⟩
    rw [GaussianInt.toComplex_def']
    calc
      (a : Complex) + (b : Complex) * Complex.I
          = (a : Complex) + Complex.I * (b : Complex) := by ring
      _ = A i j := hab.symm
  let B : Matrix α α GaussianInt := fun i j => Classical.choose (hentry_exists i j)
  have hentry (i j : α) : (B.map GaussianInt.toComplex) i j = A i j := by
    change GaussianInt.toComplex (B i j) = A i j
    exact Classical.choose_spec (hentry_exists i j)
  have hmap : GaussianInt.toComplex.mapMatrix B = A := by
    ext i j
    simpa only [RingHom.mapMatrix_apply] using hentry i j
  have hdet : A.det = (B.det : Complex) := by
    calc
      A.det = (GaussianInt.toComplex.mapMatrix B).det := by rw [hmap]
      _ = GaussianInt.toComplex B.det := by rw [← RingHom.map_det]
  refine ⟨B.det.re, B.det.im, ?_⟩
  simpa [GaussianInt.toComplex_def, mul_comm] using hdet