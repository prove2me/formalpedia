-- Prove2me | solution 1 for MIPRE.mulVec_kron_kron_expVec
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:41.146794+00:00
-- url     : https://prove2.me/submissions/04978f80-46f4-4b5a-ac07-da11e0e2efcd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Expanded.lean (solution of MIPRE.mulVec_kron_kron_expVec);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Expanded

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
/-- A product of sums as a sum over the product. -/
theorem sum_prod_mul {X Y M : Type*} [Fintype X] [Fintype Y] [CommRing M] (f : X → M)
    (g : Y → M) : ∑ q : X × Y, f q.1 * g q.2 = (∑ x, f x) * ∑ y, g y := by
  rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']
theorem _root_.solution (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) (X : Matrix dA dA ℂ)
    (Y : Matrix anc anc ℂ) (X' : Matrix dB dB ℂ) (Y' : Matrix anc' anc' ℂ) :
    (((X ⊗ₖ Y) ⊗ₖ (X' ⊗ₖ Y')) *ᵥ expVec ψ e)
      = expVec ((X ⊗ₖ X') *ᵥ ψ) ((Y ⊗ₖ Y') *ᵥ e) := by
  classical
  funext p
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := p
  show ∑ q : (dA × anc) × (dB × anc'),
      ((X ⊗ₖ Y) ⊗ₖ (X' ⊗ₖ Y')) ((a, x), (b, y)) q * expVec ψ e q
    = (∑ q : dA × dB, (X ⊗ₖ X') (a, b) q * ψ q)
      * ∑ q : anc × anc', (Y ⊗ₖ Y') (x, y) q * e q
  rw [← sum_prod_mul]
  refine Fintype.sum_equiv (expEquiv dA dB anc anc') _ _ fun q => ?_
  obtain ⟨⟨a₁, x₁⟩, ⟨b₁, y₁⟩⟩ := q
  simp only [expEquiv, Equiv.coe_fn_mk]
  show (X a a₁ * Y x x₁) * (X' b b₁ * Y' y y₁) * (ψ (a₁, b₁) * e (x₁, y₁))
    = (X a a₁ * X' b b₁) * ψ (a₁, b₁) * ((Y x x₁ * Y' y y₁) * e (x₁, y₁))
  ring
end MIPRE
