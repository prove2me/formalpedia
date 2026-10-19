-- Prove2me | solution 1 for MIPRE.sum_bornProb_mapA
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:36.973034+00:00
-- url     : https://prove2.me/submissions/4234aa2a-27d8-427f-b67d-e2b9d3164fe7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.sum_bornProb_mapA);
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
theorem sum_kronecker_left {dA dB ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) : (∑ i ∈ s, f i) ⊗ₖ N = ∑ i ∈ s, f i ⊗ₖ N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_kronecker, ih, Finset.sum_insert hi]
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
omit [Fintype X] [Fintype Y] [DecidableEq C] [DecidableEq dB] in
theorem _root_.solution {A' : Type*} [Fintype A'] [DecidableEq A'] (NA : POVM A dA)
    (φA : A → A') (EB : Matrix dB dB ℂ) (w : A' → ℝ) :
    ∑ a', w a' * bornProb ψ (((NA.map φA).mats a').val) EB
      = ∑ a, w (φA a) * bornProb ψ ((NA.mats a).val) EB := by
  classical
  have hval : ∀ a', (((NA.map φA).mats a').val)
      = ∑ a ∈ univ.filter fun a => φA a = a', ((NA.mats a).val) := fun a' => by
    rw [show ((NA.map φA).mats a') = ∑ a ∈ univ.filter fun a => φA a = a', NA.mats a from rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  have hborn : ∀ a', bornProb ψ (((NA.map φA).mats a').val) EB
      = ∑ a ∈ univ.filter fun a => φA a = a', bornProb ψ ((NA.mats a).val) EB := by
    intro a'
    simp only [bornProb]
    rw [hval a', sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => by rw [hborn a', Finset.mul_sum]]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq univ (φA a) _]
  simp only [mem_univ, if_true]
end MIPRE
