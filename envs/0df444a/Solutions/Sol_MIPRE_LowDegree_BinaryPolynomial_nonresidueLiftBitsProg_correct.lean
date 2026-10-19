-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:30:16.145282+00:00
-- url     : https://prove2.me/submissions/1f6bccd7-5aed-4570-984f-6b33591fd3e6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryNonresidueCorrectness.lean (solution of MIPRE.LowDegree.BinaryPolynomial.nonresidueLiftBitsProg_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_cyclotomicSeedBits_canonical
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_cyclotomicSeedBits_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_nonresidueInvariant_stopped
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_nonresidueStep_invariant

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A list with a true leading bit decomposes into its lower coefficients and that bit. -/
theorem dropLast_append_true (a : BitStr) (h : a.getLastD false = true) :
    a.dropLast ++ [true] = a := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hh : a.getLast hn = true := by
    cases a with
    | nil => exact (hn rfl).elim
    | cons b a => simpa only [List.getLast_eq_getLastD, List.getLastD_cons] using h
  simpa only [hh] using List.dropLast_append_getLast hn
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- A coefficient list with leading bit one represents a monic polynomial. -/
theorem monic_polyOfBits_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).Monic := by
  rw [← dropLast_append_true a h]
  exact monic_polyOfBits_append_true _
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- For a nonzero canonical representation, width is degree plus one. -/
theorem natDegree_add_one_of_getLast (a : BitStr) (h : a.getLastD false = true) :
    (polyOfBits a).natDegree + 1 = a.length := by
  have hn : a ≠ [] := by intro he; simp [he] at h
  have hl : 0 < a.length := List.length_pos_iff.mpr hn
  have hd := natDegree_polyOfBits_append_true a.dropLast
  rw [dropLast_append_true a h, List.length_dropLast] at hd
  omega
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- The bounded loop preserves its invariant with one progress count per fuel bit. -/
theorem fold_nonresidueStep_invariant (l : BitStr) (q m i : ℕ) (s : NonresidueState)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s) :
    NonresidueInvariant q m (i + l.length) (l.foldl nonresidueStep s) := by
  induction l generalizing i s with
  | nil => simpa using hv
  | cons b l ih =>
    have h := ih (i + 1) (nonresidueStep s b)
      (nonresidueStep_invariant q m i s b hq hq2 hv)
    simpa only [List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 l.length] using h
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Polynomial
/-- Explicit execution of the seed-initialized auxiliary loop. -/
theorem nonresidueLiftStateProg_apply (u : Unary) :
    nonresidueLiftStateProg u = (cyclotomicSeedBits u).tail.foldl nonresidueStep
      (u.tail, unary (cyclotomicSeedBits u).length, false, cyclotomicSeedBits u) := by
  simp only [nonresidueLiftStateProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.tail_apply,
    Cost.PolyTimeFun.length_apply, Cost.PolyTimeFun.const_apply,
    cyclotomicSeedBitsProg_apply, nonresidueLoopProg_apply]
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Polynomial
theorem _root_.solution (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) :
    let f := polyOfBits (nonresidueLiftBitsProg (unary q))
    (nonresidueLiftBitsProg (unary q)).getLastD false = true ∧
    f.Monic ∧ Irreducible f ∧
    f.natDegree = (polyOfBits (cyclotomicSeedBits (unary q))).natDegree ∧
    ∀ b : AdjoinRoot f, b ^ q ≠ AdjoinRoot.root f := by
  let a := cyclotomicSeedBits (unary q)
  let m := (polyOfBits a).natDegree
  let s : NonresidueState := ((unary q).tail, unary a.length, false, a)
  have ha := cyclotomicSeedBits_canonical q hq hq2
  have hc := cyclotomicSeedBits_correct q hq hq2
  have hlen : a.length = m + 1 := (natDegree_add_one_of_getLast a ha).symm
  have hv : NonresidueInvariant q m 0 s := by
    refine ⟨?_, ?_, ha, hc.2.1, rfl, by intro h; contradiction, ?_⟩
    · change (unary q).tail.length + 1 = q
      rw [List.length_tail, length_unary]
      exact Nat.sub_add_cancel hq.one_le
    · change (unary a.length).length = m + 1
      rw [length_unary, hlen]
    · intro _
      simpa only [Nat.zero_add, pow_one] using hc.2.2
  have hvf := fold_nonresidueStep_invariant a.tail q m 0 s hq hq2 hv
  have hbudget : a.tail.length = m := by rw [List.length_tail, hlen]; omega
  have hdone := nonresidueInvariant_stopped q m (0 + a.tail.length)
    (a.tail.foldl nonresidueStep s) hq hq2 hvf (by omega)
  have hout : nonresidueLiftBitsProg (unary q) =
      (a.tail.foldl nonresidueStep s).2.2.2 := by
    simp only [nonresidueLiftBitsProg, Cost.PolyTimeFun.comp_apply,
      Cost.PolyTimeFun.snd_apply, nonresidueLiftStateProg_apply]
    rfl
  dsimp only
  rw [hout]
  exact ⟨hvf.canonical, monic_polyOfBits_of_getLast _ hvf.canonical,
    hvf.irreducible, hvf.degree, hvf.stopped hdone⟩
end MIPRE.LowDegree.BinaryPolynomial
