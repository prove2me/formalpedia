-- Prove2me | solution 1 for MIPRE.sum_bornProb_map
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:33.565731+00:00
-- url     : https://prove2.me/submissions/0fe35ccc-1f08-4a4d-aee2-4b15c4c81e0c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.sum_bornProb_map);
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
omit [Fintype X] [Fintype Y] in
theorem _root_.solution {x : X} {y : Y} (f : A → C) (g : B → C) :
    ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
  classical
  have hvalA : ∀ c, ((((MA x).map f).mats c).val)
      = ∑ a ∈ univ.filter fun a => f a = c, (((MA x).mats a).val) := fun c => by
    rw [show (((MA x).map f).mats c) = ∑ a ∈ univ.filter fun a => f a = c, (MA x).mats a from
      rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  have hvalB : ∀ c, ((((MB y).map g).mats c).val)
      = ∑ b ∈ univ.filter fun b => g b = c, (((MB y).mats b).val) := fun c => by
    rw [show (((MB y).map g).mats c) = ∑ b ∈ univ.filter fun b => g b = c, (MB y).mats b from
      rfl]
    exact AddSubmonoidClass.coe_finsetSum _ _
  -- the Born probability of a coarse-grained outcome is the sum over its fibre
  have hborn : ∀ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      = ∑ a ∈ univ.filter fun a => f a = c, ∑ b ∈ univ.filter fun b => g b = c,
          bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    intro c
    simp only [bornProb]
    rw [hvalA c, hvalB c, sum_kronecker_left, sum_quadForm ψ _ _, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [kronecker_sum_right, sum_quadForm ψ _ _, Complex.re_sum]
  -- and the fibres of the two post-processings regroup into the agreement indicator
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hborn c]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq univ (f a) _]
  simp only [mem_univ, if_true]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : f a = g b
  · rw [if_pos h.symm, if_pos h, one_mul]
  · rw [if_neg fun hh : g b = f a => h hh.symm, if_neg h, zero_mul]
end MIPRE
