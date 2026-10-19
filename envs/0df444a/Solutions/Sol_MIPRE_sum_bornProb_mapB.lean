-- Prove2me | solution 1 for MIPRE.sum_bornProb_mapB
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:34.279351+00:00
-- url     : https://prove2.me/submissions/cb6e3a09-709a-466b-b2a9-e17fc541b89d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.sum_bornProb_mapB);
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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem sum_quadForm {N ι : Type*} [Fintype N] (ψ : N → ℂ) (s : Finset ι)
    (f : ι → Matrix N N ℂ) :
    star ψ ⬝ᵥ ((∑ i ∈ s, f i) *ᵥ ψ) = ∑ i ∈ s, star ψ ⬝ᵥ ((f i) *ᵥ ψ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem kronecker_sum_right {dA dB ι : Type*} (M : Matrix dA dA ℂ) (s : Finset ι)
    (f : ι → Matrix dB dB ℂ) : M ⊗ₖ (∑ i ∈ s, f i) = ∑ i ∈ s, M ⊗ₖ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.kronecker_add, ih, Finset.sum_insert hi]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
omit [Fintype X] [Fintype Y] [DecidableEq C] [DecidableEq dA] in
theorem _root_.solution {B' : Type*} [Fintype B'] [DecidableEq B'] (EA : Matrix dA dA ℂ)
    (NB : POVM B dB) (φB : B → B') (w : B' → ℝ) :
    ∑ b', w b' * bornProb ψ EA (((NB.map φB).mats b').val)
      = ∑ b, w (φB b) * bornProb ψ EA ((NB.mats b).val) := by
  classical
  have hval : ∀ b', (((NB.map φB).mats b').val)
      = ∑ b ∈ univ.filter fun b => φB b = b', ((NB.mats b).val) := fun b' => by
    rw [show ((NB.map φB).mats b') = ∑ b ∈ univ.filter fun b => φB b = b', NB.mats b from rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  have hborn : ∀ b', bornProb ψ EA (((NB.map φB).mats b').val)
      = ∑ b ∈ univ.filter fun b => φB b = b', bornProb ψ EA ((NB.mats b).val) := by
    intro b'
    simp only [bornProb]
    rw [hval b', kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
  rw [Finset.sum_congr rfl fun b' (_ : b' ∈ univ) => by rw [hborn b', Finset.mul_sum]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq univ (φB b) _]
  simp only [mem_univ, if_true]
end MIPRE
