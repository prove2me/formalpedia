-- Prove2me | solution 1 for MIPRE.bornProb_swapVec
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:37:26.8581+00:00
-- url     : https://prove2.me/submissions/95bf6bdd-0e4d-4113-bbba-54b86a2ae147

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Swap.lean (solution of MIPRE.bornProb_swapVec);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Swap

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem _root_.solution (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (swapVec ψ) EB EA = bornProb ψ EA EB := by
  classical
  have inner : ∀ (i : dA) (j : dB),
      (((EB ⊗ₖ EA) *ᵥ swapVec ψ) (j, i)) = (((EA ⊗ₖ EB) *ᵥ ψ) (i, j)) := by
    intro i j
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    refine Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun q => ?_
    obtain ⟨l, k⟩ := q
    show (EB ⊗ₖ EA) (j, i) (l, k) * (swapVec ψ) (l, k)
        = (EA ⊗ₖ EB) (i, j) (k, l) * ψ (k, l)
    show EB j l * EA i k * ψ (k, l) = EA i k * EB j l * ψ (k, l)
    ring
  have key : star (swapVec ψ) ⬝ᵥ ((EB ⊗ₖ EA) *ᵥ swapVec ψ)
      = star ψ ⬝ᵥ ((EA ⊗ₖ EB) *ᵥ ψ) := by
    rw [dotProduct, dotProduct]
    refine Fintype.sum_equiv (Equiv.prodComm dB dA) _ _ fun p => ?_
    obtain ⟨j, i⟩ := p
    show star (swapVec ψ) (j, i) * (((EB ⊗ₖ EA) *ᵥ swapVec ψ) (j, i))
        = star ψ (i, j) * (((EA ⊗ₖ EB) *ᵥ ψ) (i, j))
    rw [inner i j]
    rfl
  rw [bornProb, bornProb, key]
end MIPRE
