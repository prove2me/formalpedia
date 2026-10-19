-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryArtinSchreier.towerStepBits_monic_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:22.927624+00:00
-- url     : https://prove2.me/submissions/2bda678a-81cb-49c4-bffd-0c4193dbaf05

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean (solution of MIPRE.LowDegree.BinaryArtinSchreier.towerStepBits_monic_natDegree);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_polyOfBits_substituteArtinSchreierBits

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFintype
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFiniteDimensional
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientCharP
theorem _root_.solution (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (hp : p ≠ []) :
    (polyOfBits (towerStepBits p)).Monic ∧
      (polyOfBits (towerStepBits p)).natDegree = 2 * p.length := by
  obtain ⟨hg, hd, _⟩ := parameterOrbitBits_spec p hp
  have hq : (X ^ 2 + X : (ZMod 2)[X]).Monic := by
    simpa [quadratic] using quadratic_monic (0 : ZMod 2)
  have hqd : (X ^ 2 + X : (ZMod 2)[X]).natDegree = 2 := by
    simpa [quadratic] using quadratic_natDegree (0 : ZMod 2)
  change (polyOfBits (substituteArtinSchreierBits (parameterOrbitBits p))).Monic ∧ _
  rw [polyOfBits_substituteArtinSchreierBits]
  constructor
  · exact hg.comp hq (by rw [hqd]; decide)
  · rw [towerStepBits, polyOfBits_substituteArtinSchreierBits, natDegree_comp, hqd]
    change (polyOfBits (parameterOrbitBits p)).natDegree * 2 = _
    rw [hd, Nat.mul_comm]
end MIPRE.LowDegree.BinaryArtinSchreier
