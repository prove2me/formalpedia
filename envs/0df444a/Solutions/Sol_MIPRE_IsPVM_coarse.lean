-- Prove2me | solution 1 for MIPRE.IsPVM.coarse
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:09.446+00:00
-- url     : https://prove2.me/submissions/f476c7a8-6931-4122-a367-d2d04b130331

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/PVM.lean (solution of MIPRE.IsPVM.coarse);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_PVM
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.IsPVM
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
theorem _root_.solution {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ'] (h : IsPVM P) (f : Λ → Λ') :
    IsPVM (fun c => ∑ a ∈ univ.filter fun a => f a = c, P a) where
  isSelfAdjoint c := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun a _ => h.isSelfAdjoint a
  idem c := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single_of_mem a ha
      (fun a' _ ha' => h.orthogonal ha'.symm)]
    exact h.idem a
  sum_eq_one := by
    rw [Finset.sum_fiberwise (univ : Finset Λ) f P]
    exact h.sum_eq_one
end MIPRE.IsPVM
