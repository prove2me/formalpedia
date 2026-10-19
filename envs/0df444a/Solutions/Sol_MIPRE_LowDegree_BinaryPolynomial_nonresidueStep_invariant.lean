-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryPolynomial.nonresidueStep_invariant
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:24:32.847247+00:00
-- url     : https://prove2.me/submissions/6c1aa9f0-1b43-40c3-a414-ff1441db5e26

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryNonresidueCorrectness.lean (solution of MIPRE.LowDegree.BinaryPolynomial.nonresidueStep_invariant);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_liftCandidates_degree
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_liftCandidates_spec
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_lifted_factor_dvd_cyclotomic
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_monic_polyOfBits_append_true
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true

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
open Cost Cost.PolyTimeFun Polynomial
/-- Stopping is absorbing, so padding the iteration budget is harmless. -/
theorem nonresidueStep_done (s : NonresidueState) (b : Bool) (hs : s.2.2.1 = true) :
    nonresidueStep s b = s := by simp [nonresidueStep, hs]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- An irreducible monic polynomial cannot have a root in a smaller-dimensional extension. -/
theorem aeval_ne_zero_of_finrank_lt {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (g : Polynomial F) (hg : g.Monic) (hi : Irreducible g)
    (hd : Module.finrank F K < g.natDegree) (x : K) : aeval x g ≠ 0 := by
  intro hx
  have he := minpoly.eq_of_irreducible_of_monic hi hx hg
  rw [he] at hd
  exact (not_lt_of_ge (minpoly.natDegree_le (A := F) x)) hd
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Polynomial
/-- Irreducibility of the substituted polynomial certifies a nonresidue at the old root.
This is the soundness of the executable singleton-factor stopping test. -/
theorem nonresidue_of_irreducible_comp {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (f : Polynomial F) (hf : f.Monic)
    (hd : Module.finrank F K = f.natDegree) (hp : 0 < f.natDegree)
    (q : ℕ) (hq : 1 < q) (a : K) (ha : aeval a f = 0)
    (hi : Irreducible (f.comp (X ^ q))) : ∀ b : K, b ^ q ≠ a := by
  intro b hb
  have hq0 : q ≠ 0 := by omega
  have hm : (f.comp (X ^ q)).Monic := hf.comp (monic_X.pow q) (by simpa using hq0)
  have hdeg : Module.finrank F K < (f.comp (X ^ q)).natDegree := by
    rw [hd, natDegree_comp, natDegree_X_pow]
    nlinarith
  apply aeval_ne_zero_of_finrank_lt (f.comp (X ^ q)) hm hi hdeg b
  rw [aeval_def, eval₂_comp]
  simpa only [eval₂_pow, eval₂_X, hb, ← aeval_def] using ha
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryPolynomial
open Cost Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.solution (q m i : ℕ) (s : NonresidueState) (b : Bool)
    (hq : q.Prime) (hq2 : q ≠ 2) (hv : NonresidueInvariant q m i s) :
    NonresidueInvariant q m (i + 1) (nonresidueStep s b) := by
  cases hd : s.2.2.1 with
  | true =>
    rw [nonresidueStep_done s b hd]
    exact ⟨hv.exponent, hv.cap, hv.canonical, hv.irreducible, hv.degree,
      hv.stopped, by intro h; rw [hd] at h; contradiction⟩
  | false =>
    have hs := liftCandidates_spec q m i s hq hq2 hv hd
    cases ht : (liftCandidates s).tail.isEmpty with
    | true =>
      have he : nonresidueStep s b = (s.1, s.2.1, true, s.2.2.2) := by
        simp [nonresidueStep, hd, ht]
      rw [he]
      refine ⟨hv.exponent, hv.cap, hv.canonical, hv.irreducible, hv.degree, ?_,
        by intro h; contradiction⟩
      intro _
      let f := polyOfBits s.2.2.2
      let : Fact (Irreducible f) := ⟨hv.irreducible⟩
      let : Module.Finite (ZMod 2) (AdjoinRoot f) :=
        (AdjoinRoot.powerBasis hv.irreducible.ne_zero).finite
      exact nonresidue_of_irreducible_comp f (monic_polyOfBits_of_getLast _ hv.canonical)
        (AdjoinRoot.powerBasis hv.irreducible.ne_zero).finrank hv.irreducible.natDegree_pos
        q hq.one_lt (AdjoinRoot.root f) (by simp) (hs.2.2.2.mp ht)
    | false =>
      let a := (liftCandidates s).headD []
      have ha : a ∈ liftCandidates s := by
        cases hl : liftCandidates s with
        | nil => exact (hs.1 hl).elim
        | cons c l => simp [a, hl]
      have hac := hs.2.2.1 a ha
      have had := liftCandidates_degree q m i s hq hq2 hv hd ht a ha
      have hal : a.length = m + 1 := by
        rw [← natDegree_add_one_of_getLast a hac.1, had]
      have htake : a.take s.2.1.length = a := by
        apply List.take_of_length_le
        rw [hal, hv.cap]
      have he : nonresidueStep s b = (s.1, s.2.1, false, a) := by
        simp only [nonresidueStep, hd, ht, Bool.false_eq_true, if_false]
        change (s.1, s.2.1, false, a.take s.2.1.length) = (s.1, s.2.1, false, a)
        rw [htake]
      rw [he]
      refine ⟨hv.exponent, hv.cap, hac.1, hac.2.2, had, by intro h; contradiction, ?_⟩
      intro _
      apply lifted_factor_dvd_cyclotomic _ _ q (i + 1) hq hq2 (by omega) hac.2.2
        (hv.running hd)
      rw [← hs.2.1]
      exact List.dvd_prod (List.mem_map.mpr ⟨a, ha, rfl⟩)
end MIPRE.LowDegree.BinaryPolynomial
