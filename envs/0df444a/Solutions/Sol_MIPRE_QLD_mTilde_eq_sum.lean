-- Prove2me | solution 1 for MIPRE.QLD.mTilde_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:30.719989+00:00
-- url     : https://prove2.me/submissions/6fb344ad-fa2b-4c00-8dfd-c65e211afad0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/ExactPauli.lean (solution of MIPRE.QLD.mTilde_eq_sum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Background_QLD_ExactPauli

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
/-- `(sum_x A x) (x) B = sum_x (A x (x) B)`. -/
theorem sum_kron {iota : Type*} (s : Finset iota) (A : iota → Matrix dA dA ℂ)
    (B : Matrix (n → F) (n → F) ℂ) :
    (∑ x ∈ s, A x) ⊗ₖ B = ∑ x ∈ s, A x ⊗ₖ B := by
  ext p q
  obtain ⟨a, k⟩ := p
  obtain ⟨b, l⟩ := q
  rw [Matrix.kronecker_apply, Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => (Matrix.kronecker_apply _ _ _ _ _ _).symm
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
/-- **Summing a family against the marginals is summing it against the measurement**, the label
read off through the projection. The fibrewise sum, stated once because both the definition of
`mTilde` and its factorization use it. -/
theorem sum_sCoarse_kron {S : G × G → Matrix dA dA ℂ} (pi : G × G → G)
    (T : G → Matrix (n → F) (n → F) ℂ) :
    ∑ g, sCoarse S pi g ⊗ₖ T g = ∑ p, S p ⊗ₖ T (pi p) := by
  classical
  rw [show ∑ p, S p ⊗ₖ T (pi p)
      = ∑ g, ∑ p ∈ univ.filter fun p => pi p = g, S p ⊗ₖ T (pi p) from
    (Finset.sum_fiberwise (univ : Finset (G × G)) pi fun p => S p ⊗ₖ T (pi p)).symm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [sCoarse, sum_kron]
  exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
  (w : (n → F) → Matrix (n → F) (n → F) ℂ)
theorem _root_.solution (u : n → F) (a : F) :
    mTilde S pi cd w u a = ∑ p, S p ⊗ₖ syn w u (dotF (cd (pi p)) u + a) :=
  sum_sCoarse_kron pi _
end MIPRE.QLD
