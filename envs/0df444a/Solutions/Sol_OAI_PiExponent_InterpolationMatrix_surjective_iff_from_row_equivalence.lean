-- Prove2me | solution 1 for OAI.PiExponent.InterpolationMatrix.surjective_iff_from_row_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:22:19.601994+00:00
-- url     : https://prove2.me/submissions/8ea2e072-c3b4-4df6-b2f1-f6e48b22744b

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem solution
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι ι ℂ) (M M' : Matrix ι κ ℂ)
    (hU : Function.Bijective U.mulVecLin) (hfactor : M = U * M') :
    Function.Surjective M.mulVecLin ↔ Function.Surjective M'.mulVecLin := by
  subst hfactor
  have h : (U * M').mulVecLin = U.mulVecLin ∘ M'.mulVecLin := by
    rw [Matrix.mulVecLin_mul]; rfl
  rw [h]
  constructor
  · intro hs y
    obtain ⟨x, hx⟩ := hs (U.mulVecLin y)
    exact ⟨x, hU.1 hx⟩
  · intro hs
    exact hU.2.comp hs
