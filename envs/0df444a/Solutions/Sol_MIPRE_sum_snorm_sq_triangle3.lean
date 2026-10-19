-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_triangle3
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:51.654571+00:00
-- url     : https://prove2.me/submissions/5440d2fa-ad7d-459f-b12b-d6e5635dcc89

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.sum_snorm_sq_triangle3);
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
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem _root_.solution {κ : Type*} [Fintype κ] (v : N → ℂ)
    (P Q R T : κ → Matrix N N ℂ) :
    ∑ o, snorm v (P o - T o) ^ 2
      ≤ 3 * ∑ o, snorm v (P o - Q o) ^ 2 + 3 * ∑ o, snorm v (Q o - R o) ^ 2
        + 3 * ∑ o, snorm v (R o - T o) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun o _ => ?_
  have hsplit : P o - T o = (P o - Q o) + ((Q o - R o) + (R o - T o)) := by abel
  have htri : snorm v (P o - T o)
      ≤ snorm v (P o - Q o) + (snorm v (Q o - R o) + snorm v (R o - T o)) := by
    rw [hsplit]
    exact le_trans (snorm_add_le v _ _) (by
      have := snorm_add_le v (Q o - R o) (R o - T o)
      linarith)
  nlinarith [snorm_nonneg v (P o - Q o), snorm_nonneg v (Q o - R o), snorm_nonneg v (R o - T o),
    snorm_nonneg v (P o - T o), sq_nonneg (snorm v (P o - Q o) - snorm v (Q o - R o)),
    sq_nonneg (snorm v (P o - Q o) - snorm v (R o - T o)),
    sq_nonneg (snorm v (Q o - R o) - snorm v (R o - T o))]
end MIPRE
