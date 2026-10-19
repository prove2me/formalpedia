-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.fold_assemblyStep_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:07:40.047997+00:00
-- url     : https://prove2.me/submissions/ef21275b-c2a9-4723-925e-0b2ec221766a

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryIrreducibleAssembly.lean (solution of MIPRE.LowDegree.BinaryPolynomial.fold_assemblyStep_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_composedLowerBits_correct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryQuotient DegreeArithmetic
/-- The cap is inert whenever the intended next degree is within the target. -/
theorem assemblyStep_correct (u : Unary) (p g : BitStr)
    (hp : Irreducible (polyOfBits (p ++ [true])))
    (hg : (polyOfBits g).Monic) (hgi : Irreducible (polyOfBits g))
    (hcop : p.length.Coprime (polyOfBits g).natDegree)
    (hcap : p.length * (polyOfBits g).natDegree ≤ u.length) :
    Irreducible (polyOfBits ((assemblyStep (u, p) g).2 ++ [true])) ∧
      (assemblyStep (u, p) g).2.length = p.length * (polyOfBits g).natDegree := by
  have h := composedLowerBits_correct p g hp hg hgi hcop
  have ht : (composedLowerBits p g).take u.length = composedLowerBits p g :=
    List.take_of_length_le (h.2.trans_le hcap)
  simpa only [assemblyStep, ht] using h
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Cost.PolyTimeFun Polynomial BinaryQuotient DegreeArithmetic
theorem _root_.solution (l : List BitStr) (u : Unary) (p : BitStr)
    (hp : Irreducible (polyOfBits (p ++ [true])))
    (hl : ∀ g ∈ l, (polyOfBits g).Monic ∧ Irreducible (polyOfBits g))
    (hpair : l.Pairwise (fun g h => (polyOfBits g).natDegree.Coprime (polyOfBits h).natDegree))
    (hcop : ∀ g ∈ l, p.length.Coprime (polyOfBits g).natDegree)
    (hcap : p.length * (l.map (fun g => (polyOfBits g).natDegree)).prod ≤ u.length) :
    Irreducible (polyOfBits ((l.foldl assemblyStep (u, p)).2 ++ [true])) ∧
      (l.foldl assemblyStep (u, p)).2.length =
        p.length * (l.map (fun g => (polyOfBits g).natDegree)).prod := by
  induction l generalizing p with
  | nil => simpa using hp
  | cons g l ih =>
    have hg := hl g (by simp)
    have htail : ∀ a ∈ l, (polyOfBits a).Monic ∧ Irreducible (polyOfBits a) :=
      fun a ha => hl a (by simp [ha])
    obtain ⟨hhead, hpairs⟩ := List.pairwise_cons.mp hpair
    have hpos := degree_prod_pos l (fun a ha => (htail a ha).2)
    have hbound : p.length * (polyOfBits g).natDegree ≤ u.length := by
      simp only [List.map_cons, List.prod_cons, ← Nat.mul_assoc] at hcap
      have hmul := Nat.le_mul_of_pos_right (p.length * (polyOfBits g).natDegree) hpos
      exact hmul.trans hcap
    have hs := assemblyStep_correct u p g hp hg.1 hg.2 (hcop g (by simp)) hbound
    let p' := (assemblyStep (u, p) g).2
    have hcop' : ∀ a ∈ l, p'.length.Coprime (polyOfBits a).natDegree := by
      intro a ha
      change (assemblyStep (u, p) g).2.length.Coprime _
      rw [hs.2]
      exact (hcop a (by simp [ha])).mul_left (hhead a ha)
    have hcap' : p'.length * (l.map (fun a => (polyOfBits a).natDegree)).prod ≤ u.length := by
      change (assemblyStep (u, p) g).2.length * _ ≤ _
      rw [hs.2]
      simpa only [List.map_cons, List.prod_cons, Nat.mul_assoc] using hcap
    have hout := ih p' hs.1 htail hpairs hcop' hcap'
    change Irreducible (polyOfBits ((l.foldl assemblyStep (u, p')).2 ++ [true])) ∧ _
    refine ⟨hout.1, ?_⟩
    change (l.foldl assemblyStep (u, p')).2.length = _
    rw [hout.2]
    change (assemblyStep (u, p) g).2.length * _ = _
    rw [hs.2]
    simp only [List.map_cons, List.prod_cons, Nat.mul_assoc]
end MIPRE.LowDegree.BinaryPolynomial
