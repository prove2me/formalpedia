-- Prove2me | solution 1 for MIPRE.Introspection.qform_state_stability
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:19:11.5207+00:00
-- url     : https://prove2.me/submissions/df21339b-438d-4906-b863-e4d9be80282e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/StateStability.lean (solution of MIPRE.Introspection.qform_state_stability);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
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
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
theorem inner_evec (u w : N → ℂ) : (inner ℂ (evec u) (evec w) : ℂ) = star u ⬝ᵥ w := by
  rw [evec, evec, EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
theorem _root_.solution (v w : N → ℂ) (hv : ‖evec v‖ = 1) (hw : ‖evec w‖ = 1)
    (R : Matrix N N ℂ) (hR : Bnd R 1) :
    |qform v R - qform w R| ≤ 2 * ‖evec (v - w)‖ := by
  have hcs (x y : N → ℂ) : |(star x ⬝ᵥ y).re| ≤ ‖evec x‖ * ‖evec y‖ := by
    rw [← inner_evec]
    exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hvR : ‖evec (R *ᵥ v)‖ ≤ 1 := by simpa only [hv, one_mul] using hR v
  have hdR : ‖evec (R *ᵥ (v - w))‖ ≤ ‖evec (v - w)‖ := by
    simpa only [one_mul] using hR (v - w)
  have h1 : |(star (v - w) ⬝ᵥ (R *ᵥ v)).re| ≤ ‖evec (v - w)‖ :=
    (hcs _ _).trans (by nlinarith [norm_nonneg (evec (v - w))])
  have h2 : |(star w ⬝ᵥ (R *ᵥ (v - w))).re| ≤ ‖evec (v - w)‖ := by
    have h := hcs w (R *ᵥ (v - w))
    rw [hw, one_mul] at h
    exact h.trans hdR
  have heq : qform v R - qform w R =
      (star (v - w) ⬝ᵥ (R *ᵥ v)).re + (star w ⬝ᵥ (R *ᵥ (v - w))).re := by
    simp only [qform, star_sub, sub_dotProduct, Matrix.mulVec_sub,
      dotProduct_sub, Complex.sub_re]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)
end MIPRE.Introspection
