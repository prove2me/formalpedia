-- Prove2me | solution 1 for LinearIdentifiability.model_exp_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T09:15:48.514267+00:00
-- url     : https://prove2.me/submissions/c1e2bc87-e16a-4be8-891f-4f33e1ae7611

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix
namespace LinearIdentifiability


theorem model_exp_form {X Y : Type*} {M : ℕ}
    (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X) (S : Finset Y) (hS : S.Nonempty) (y : Y) :
    modelProb f g x S y = Real.exp (augF f g x S ⬝ᵥ augG g y) := by
  have hpos : 0 < ∑ y' ∈ S, Real.exp (f x ⬝ᵥ g y') :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hS
  simp only [modelProb, augF, augG, logNormalizer, Matrix.cons_dotProduct_cons, mul_one]
  rw [Real.exp_add, Real.exp_neg, Real.exp_log hpos]
  ring

end LinearIdentifiability

open LinearIdentifiability in
theorem solution {X Y : Type*} {M : ℕ}
    (f : X → Fin M → ℝ) (g : Y → Fin M → ℝ) (x : X) (S : Finset Y) (hS : S.Nonempty) (y : Y) :
    modelProb f g x S y = Real.exp (augF f g x S ⬝ᵥ augG g y) := by
  have hpos : 0 < ∑ y' ∈ S, Real.exp (f x ⬝ᵥ g y') :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hS
  simp only [modelProb, augF, augG, logNormalizer, Matrix.cons_dotProduct_cons, mul_one]
  rw [Real.exp_add, Real.exp_neg, Real.exp_log hpos]
  ring
