-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryArtinSchreier.towerStepBits_cubic
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:26.345983+00:00
-- url     : https://prove2.me/submissions/bd243d5f-f169-4ec6-b4a3-d9644969940f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean (solution of MIPRE.LowDegree.BinaryArtinSchreier.towerStepBits_cubic);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_comp_quadratic_cubic_irreducible
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_polyOfBits_substituteArtinSchreierBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
/-- Transport the canonical-root cubic invariant across equality of binary moduli. -/
theorem cubic_irreducible_congr {f g : (ZMod 2)[X]} (hfg : f = g)
    (hf : Irreducible f) (hg : Irreducible g)
    (hc : let : Fact (Irreducible g) := ⟨hg⟩
      Irreducible (quadratic (AdjoinRoot.root g ^ 3 + AdjoinRoot.root g ^ 2))) :
    let : Fact (Irreducible f) := ⟨hf⟩
    Irreducible (quadratic (AdjoinRoot.root f ^ 3 + AdjoinRoot.root f ^ 2)) := by
  subst g
  exact hc
end
end MIPRE.LowDegree.BinaryArtinSchreier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFintype
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFiniteDimensional
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientCharP
set_option maxHeartbeats 2000000 in
theorem _root_.solution (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (t : ℕ) (hd : p.length = 2 ^ t)
    (hc : Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 3 +
        AdjoinRoot.root (polyOfBits (p ++ [true])) ^ 2))) :
    let : Fact (Irreducible (polyOfBits (towerStepBits p))) :=
      ⟨towerStepBits_irreducible p t hd hc⟩
    Irreducible (quadratic
      (AdjoinRoot.root (polyOfBits (towerStepBits p)) ^ 3 +
        AdjoinRoot.root (polyOfBits (towerStepBits p)) ^ 2)) := by
  have hp : p ≠ [] := List.length_pos_iff.mp (by rw [hd]; positivity)
  obtain ⟨hg, hgd, hgz⟩ := parameterOrbitBits_spec p hp
  have h := comp_quadratic_cubic_irreducible t ((quotient_finrank p).trans hd) _ hc
    (polyOfBits (parameterOrbitBits p)) hg (hgd.trans hd) hgz
  have he : polyOfBits (towerStepBits p) =
      (polyOfBits (parameterOrbitBits p)).comp (quadratic (0 : ZMod 2)) := by
    rw [towerStepBits, polyOfBits_substituteArtinSchreierBits]
    simp only [quadratic, C_0, add_zero, parameterOrbitBits]
  exact cubic_irreducible_congr he (towerStepBits_irreducible p t hd hc)
    (comp_quadratic_irreducible t ((quotient_finrank p).trans hd) _ hc
      (polyOfBits (parameterOrbitBits p)) hg (hgd.trans hd) hgz) h
end MIPRE.LowDegree.BinaryArtinSchreier
