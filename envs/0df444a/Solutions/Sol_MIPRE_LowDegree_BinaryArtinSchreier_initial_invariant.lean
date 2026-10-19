-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryArtinSchreier.initial_invariant
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:27.017995+00:00
-- url     : https://prove2.me/submissions/e1eeb307-85db-4e87-908d-d6fbf9318a7c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean (solution of MIPRE.LowDegree.BinaryArtinSchreier.initial_invariant);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_next_quadratic_irreducible

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- The polynomial used by Shoup's contract reads the same coefficient bits. -/
theorem coeff_polyOfBits (l : BitStr) (i : ℕ) :
    (polyOfBits l).coeff i = ofBool (l.getD i false) := by
  simp only [polyOfBits, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i < l.length
  · simp [hi, ofBool]
  · simp [hi, ofBool, List.getD_eq_getElem?_getD]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
theorem polyOfBits_cons (b : Bool) (l : BitStr) :
    polyOfBits (b :: l) = Polynomial.C (ofBool b) + Polynomial.X * polyOfBits l := by
  ext i
  cases i <;> simp [coeff_polyOfBits, Polynomial.coeff_X_mul]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
/-- The multiplicative next parameter is the uniform cubic expression in the new root. -/
theorem next_parameter_eq_cubic (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    algebraMap K (AdjoinRoot (quadratic a)) a * AdjoinRoot.root (quadratic a) =
      AdjoinRoot.root (quadratic a) ^ 3 + AdjoinRoot.root (quadratic a) ^ 2 := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  let : CharP (AdjoinRoot (quadratic a)) 2 := charP_of_injective_algebraMap'
    K (A := AdjoinRoot (quadratic a)) 2
  rw [← CharTwo.add_eq_zero.mp (root_relation a)]
  ring
end
end MIPRE.LowDegree.BinaryArtinSchreier

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
/-- The source's cubic expression therefore preserves the no-root invariant. -/
theorem cubic_quadratic_irreducible (a : K) (ha : Irreducible (quadratic a)) :
    let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
    Irreducible (quadratic
      (AdjoinRoot.root (quadratic a) ^ 3 + AdjoinRoot.root (quadratic a) ^ 2)) := by
  let : Fact (Irreducible (quadratic a)) := ⟨ha⟩
  rw [← next_parameter_eq_cubic a ha]
  exact next_quadratic_irreducible a ha
end
end MIPRE.LowDegree.BinaryArtinSchreier

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Polynomial Module
variable {K : Type*} [Field K]
variable [CharP K 2]
/-- The initial binary quadratic has no root. -/
theorem binary_initial_irreducible : Irreducible (quadratic (1 : ZMod 2)) := by
  apply (quadratic_irreducible_iff _).2
  decide
end
end MIPRE.LowDegree.BinaryArtinSchreier

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

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFintype
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFiniteDimensional
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientCharP
/-- The seed is the specified degree-two polynomial. -/
theorem initial_polynomial : polyOfBits [true, true, true] = quadratic (1 : ZMod 2) := by
  simp only [polyOfBits_cons, show polyOfBits [] = 0 from rfl, ofBool, if_true, mul_zero, add_zero, C_1,
    quadratic]
  ring
end
end MIPRE.LowDegree.BinaryArtinSchreier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryArtinSchreier
open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFintype
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFiniteDimensional
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientCharP
theorem _root_.solution : TowerInvariant [true, true] 0 := by
  have hi : Irreducible (polyOfBits ([true, true] ++ [true])) := by
    simpa only [List.cons_append, List.nil_append, initial_polynomial] using binary_initial_irreducible
  refine ⟨rfl, hi, ?_⟩
  exact cubic_irreducible_congr initial_polynomial hi binary_initial_irreducible
    (cubic_quadratic_irreducible (1 : ZMod 2) binary_initial_irreducible)
end MIPRE.LowDegree.BinaryArtinSchreier
