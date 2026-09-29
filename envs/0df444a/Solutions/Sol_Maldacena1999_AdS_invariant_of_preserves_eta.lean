-- Prove2me | solution 1 for Maldacena1999.AdS_invariant_of_preserves_eta
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:34:24.215515+00:00
-- url     : https://prove2.me/submissions/9ec2051c-7793-4a2d-b4c7-47dd301fa441

import Mathlib
import Definitions.Def_Maldacena1999_Defs

set_option autoImplicit false

open Filter Topology

open Maldacena1999 in
theorem solution (p : ℕ) (R : ℝ)
    (A : Matrix (Fin (p + 3)) (Fin (p + 3)) ℝ)
    (hA : A.transpose * Matrix.diagonal (ambientSign p) * A = Matrix.diagonal (ambientSign p))
    (X : Fin (p + 3) → ℝ) (hX : X ∈ AdS p R) :
    A.mulVec X ∈ AdS p R := by
  have key : ∀ Y : Fin (p + 3) → ℝ,
      ambientForm p Y = Y ⬝ᵥ (Matrix.diagonal (ambientSign p)).mulVec Y := by
    intro Y
    unfold ambientForm dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_diagonal]
    ring
  have hX' : ambientForm p X = -R ^ 2 := hX
  show ambientForm p (A.mulVec X) = -R ^ 2
  rw [key, ← hX', key, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose A X,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]
#print axioms solution
