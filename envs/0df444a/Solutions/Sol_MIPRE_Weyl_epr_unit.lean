-- Prove2me | solution 1 for MIPRE.Weyl.epr_unit
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:43:19.471987+00:00
-- url     : https://prove2.me/submissions/a6e08efd-643b-45eb-bb9a-d0e23a1ee589

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/WeylEPR.lean (solution of MIPRE.Weyl.epr_unit);
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
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_WeylEPR

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem card_ne_zero : (Fintype.card (n → F) : ℂ) ≠ 0 := by
  have : 0 < Fintype.card (n → F) := Fintype.card_pos
  exact_mod_cast this.ne'
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem eprScale_sq : (eprScale (F := F) (n := n)) ^ 2 = (Fintype.card (n → F) : ℝ)⁻¹ := by
  have hpos : (0 : ℝ) < Fintype.card (n → F) := by
    exact_mod_cast Fintype.card_pos (α := n → F)
  rw [eprScale, inv_pow, Real.sq_sqrt hpos.le]
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem _root_.solution : star (epr (F := F) (n := n)) ⬝ᵥ epr = 1 := by
  classical
  have hcard : (Fintype.card (n → F) : ℂ) ≠ 0 := card_ne_zero
  rw [dotProduct]
  have hterm : ∀ p : (n → F) × (n → F),
      star (epr (F := F) (n := n)) p * epr p
        = if p.1 = p.2 then ((eprScale (F := F) (n := n) ^ 2 : ℝ) : ℂ) else 0 := by
    intro p
    rw [Pi.star_apply, epr]
    by_cases h : p.1 = p.2
    · rw [if_pos h, if_pos h, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, sq]
    · rw [if_neg h, if_neg h, star_zero, mul_zero]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hterm p, eprScale_sq, ← Finset.sum_filter]
  have hdiag : {p ∈ (univ : Finset ((n → F) × (n → F))) | p.1 = p.2}
      = (univ : Finset (n → F)).diag := by
    ext p
    simp [Finset.mem_diag]
  rw [hdiag, Finset.sum_const, Finset.diag_card, Finset.card_univ, nsmul_eq_mul]
  push_cast
  rw [mul_inv_cancel₀ hcard]
end MIPRE.Weyl
