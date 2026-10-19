-- Prove2me | solution 1 for MIPRE.POVM.sub_mul_self_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:23.3772+00:00
-- url     : https://prove2.me/submissions/282a1ea5-e648-4dae-99cf-5b5353d7feb6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.POVM.sub_mul_self_le_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue
import Theorems.Thm_MIPRE_POVM_sum_val

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
/-- Each POVM element is at most the identity. -/
theorem POVM.le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (p : A) : ((M.mats p).val) ≤ (1 : Matrix d d ℂ) := by
  rw [← POVM.sum_val M]
  exact Finset.single_le_sum (fun a _ => Subtype.coe_le_coe.mpr (M.nonneg a)) (Finset.mem_univ p)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.POVM
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem _root_.solution {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVM A d) (p q : A) :
    (((M.mats p).val - (M.mats q).val) * ((M.mats p).val - (M.mats q).val))
      ≤ (1 : Matrix d d ℂ) := by
  set X := ((M.mats p).val - (M.mats q).val) with hX
  have h1 : (0 : Matrix d d ℂ) ≤ 1 - X := by
    have hsplit : (1 : Matrix d d ℂ) - X = (1 - (M.mats p).val) + (M.mats q).val := by
      rw [hX]; abel
    rw [hsplit]
    exact add_nonneg (sub_nonneg.mpr (M.le_one p)) (Subtype.coe_le_coe.mpr (M.nonneg q))
  have h2 : (0 : Matrix d d ℂ) ≤ 1 + X := by
    have hsplit : (1 : Matrix d d ℂ) + X = (1 - (M.mats q).val) + (M.mats p).val := by
      rw [hX]; abel
    rw [hsplit]
    exact add_nonneg (sub_nonneg.mpr (M.le_one q)) (Subtype.coe_le_coe.mpr (M.nonneg p))
  have hc : Commute ((1 : Matrix d d ℂ) - X) (1 + X) := by
    show ((1 : Matrix d d ℂ) - X) * (1 + X) = (1 + X) * (1 - X)
    noncomm_ring
  have hprod : (0 : Matrix d d ℂ) ≤ ((1 : Matrix d d ℂ) - X) * (1 + X) := hc.mul_nonneg h1 h2
  have heq : ((1 : Matrix d d ℂ) - X) * (1 + X) = 1 - X * X := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod
end MIPRE.POVM
