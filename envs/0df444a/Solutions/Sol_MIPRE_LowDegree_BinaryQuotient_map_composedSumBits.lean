-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.map_composedSumBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:31.909396+00:00
-- url     : https://prove2.me/submissions/06ea3883-c182-43bd-bba7-13f1340a5c63

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComposedSum.lean (solution of MIPRE.LowDegree.BinaryQuotient.map_composedSumBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_shiftReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_coeffPolynomial_linearMulCarry
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_coeffPolynomial_mulCoeffLists
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_evalBits_eq_head_of_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_linearMulCarry_width
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_mulCoeffLists_width
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_root_eq

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

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Repeated squaring preserves the fixed-width representation. -/
theorem iterate_squareStep_width (n : ℕ) (p a : BitStr) (ha : a.length = p.length) :
    (squareStep^[n] (p, a)).2.length = p.length := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (length_mulReduce p a a ha)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Repeated squaring computes the corresponding Frobenius power. -/
theorem evalBits_iterate_squareStep [CharP R 2] (z : R) (n : ℕ) (p a : BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (squareStep^[n] (p, a)).2 = evalBits z a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change evalBits z (squareStep^[n] (p, mulReduce p a a)).2 = _
    rw [ih _ (length_mulReduce p a a ha), evalBits_mulReduce z p a a ha hz]
    rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm (2 ^ n) 2]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Every orbit element has the supplied modulus width. -/
theorem orbitBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    ∀ b ∈ orbitBits u p a, b.length = p.length := by
  intro b hb
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  exact iterate_squareStep_width i p a ha
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- The orbit encodes exactly the specified list of Frobenius powers. -/
theorem map_evalBits_orbitBits [CharP R 2] (z : R) (u : Unary) (p a : BitStr)
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    (orbitBits u p a).map (evalBits z) =
      List.ofFn (fun i : Fin u.length => evalBits z a ^ (2 ^ (i : ℕ))) := by
  simp only [orbitBits, recordIterates, List.map_ofFn]
  congr 1
  funext i
  exact evalBits_iterate_squareStep z i p a hz ha
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Coefficients of the interpreted nested list are the decoded list entries. -/
theorem coeff_coeffPolynomial (z : R) (cs : List BitStr) (i : ℕ) :
    (coeffPolynomial z cs).coeff i = evalBits z (cs.getD i []) := by
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i => simp [coeff_X_mul, ih]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- If every coefficient is its constant coordinate, descent recovers the same polynomial. -/
theorem map_polyOfBits_descendBits [Algebra (ZMod 2) R] (z : R) (cs : List BitStr)
    (hc : ∀ c ∈ cs, evalBits z c = ofBool (c.headD false)) :
    (polyOfBits (descendBits cs)).map (algebraMap (ZMod 2) R) = coeffPolynomial z cs := by
  induction cs with
  | nil => simp [descendBits, polyOfBits]
  | cons c cs ih =>
    have h := hc c (by simp)
    have ht := ih (fun d hd => hc d (by simp [hd]))
    change (polyOfBits (c.headD false :: descendBits cs)).map _ = _
    rw [polyOfBits_cons, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, ht, coeffPolynomial_cons, h]
    cases c.headD false <;> simp [ofBool]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- Correct-width translation preserves the quotient coefficient width. -/
theorem translateBits_width (p a g : BitStr) (ha : a.length = p.length) :
    ∀ c ∈ translateBits p a g, c.length = p.length := by
  induction g with
  | nil => simp [translateBits]
  | cons b g ih =>
    apply linearMulCarry_width _ _ _ _ ha _ ih
    cases b <;> simp
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]
/-- The translation program substitutes `X+a` in the input binary polynomial. -/
theorem coeffPolynomial_translateBits (z : R) (p a g : BitStr) (hp : p ≠ [])
    (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    coeffPolynomial z (translateBits p a g) =
      ((polyOfBits g).map (algebraMap (ZMod 2) R)).comp (X + C (evalBits z a)) := by
  induction g with
  | nil => simp [translateBits, polyOfBits]
  | cons b g ih =>
    rw [translateBits, coeffPolynomial_linearMulCarry z p a _ _ hz ha
      (by cases b <;> simp) (translateBits_width p a g ha), ih, polyOfBits_cons]
    cases b <;> simp [ofBool, evalBits_oneBits z p hp, Polynomial.map_add,
      Polynomial.map_mul, add_comp, mul_comp]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryFiniteField
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
variable {L : Type*} [Field L] [Algebra (ZMod 2) L]
/-- Binary minimal degree divides exactly the Frobenius periods of an integral element. -/
theorem minpoly_natDegree_dvd_iff_frobenius (x : L) (hx : IsIntegral (ZMod 2) x) (n : ℕ) :
    (minpoly (ZMod 2) x).natDegree ∣ n ↔ x ^ (2 ^ n) = x := by
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  simp only [map_sub, map_pow, aeval_X, Nat.card_eq_fintype_card, ZMod.card, sub_eq_zero]
end
end MIPRE.LowDegree.BinaryFiniteField

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
theorem composedSumPolynomial_succ' (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    composedSumPolynomial g x (n + 1) =
      composedSumPolynomial g x n * translatedPolynomial g (x ^ (2 ^ n)) := by
  rw [composedSumPolynomial, List.ofFn_succ', List.prod_concat]
  rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
/-- Coefficient Frobenius commutes with translation of a binary polynomial. -/
theorem map_frobenius_translatedPolynomial [CharP R 2] (g : Polynomial (ZMod 2)) (x : R) :
    (translatedPolynomial g x).map (frobenius R 2) = translatedPolynomial g (x ^ 2) := by
  have hbase : (frobenius R 2).comp (algebraMap (ZMod 2) R) = algebraMap (ZMod 2) R := by
    ext z
    change (algebraMap (ZMod 2) R z) ^ 2 = algebraMap (ZMod 2) R z
    rw [← map_pow]
    have hz : z ^ 2 = z := by simp
    rw [hz]
  rw [translatedPolynomial, Polynomial.map_comp, Polynomial.map_map, hbase,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, frobenius_def]
  rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
/-- Coefficient Frobenius shifts the translate orbit by one place. -/
theorem map_frobenius_composedSumPolynomial [CharP R 2]
    (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).map (frobenius R 2) = composedSumPolynomial g (x ^ 2) n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [composedSumPolynomial_succ, Polynomial.map_mul, map_frobenius_translatedPolynomial,
      ih, composedSumPolynomial_succ]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
/-- Closing the translate orbit fixes every product coefficient under Frobenius. -/
theorem map_frobenius_composedSumPolynomial_of_closed [IsDomain R] [CharP R 2]
    (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) :
    (composedSumPolynomial g x n).map (frobenius R 2) = composedSumPolynomial g x n := by
  rw [map_frobenius_composedSumPolynomial]
  apply mul_left_cancel₀ (translatedPolynomial_monic g hg x).ne_zero
  rw [← composedSumPolynomial_succ, composedSumPolynomial_succ', hx, mul_comm]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
/-- The coefficients of a closed product of binary translates are binary. -/
theorem composedSumPolynomial_coeff_zero_or_one [IsDomain R] [CharP R 2]
    (g : Polynomial (ZMod 2)) (hg : g.Monic) (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) (i : ℕ) :
    (composedSumPolynomial g x n).coeff i = 0 ∨ (composedSumPolynomial g x n).coeff i = 1 := by
  have h := congrArg (fun p : Polynomial R => p.coeff i)
    (map_frobenius_composedSumPolynomial_of_closed g hg x n hx)
  rw [coeff_map, frobenius_def] at h
  have hz : (composedSumPolynomial g x n).coeff i * ((composedSumPolynomial g x n).coeff i - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
/-- Valid quotient widths are preserved by the translate-product loop. -/
theorem fold_normStep_width (pre : List BitStr) (p g : BitStr) (cs : List BitStr)
    (ha : ∀ a ∈ pre, a.length = p.length) (hc : ∀ c ∈ cs, c.length = p.length) :
    ∀ c ∈ (pre.foldl normStep (p, g, cs)).2.2, c.length = p.length := by
  induction pre generalizing cs with
  | nil => exact hc
  | cons a pre ih =>
    apply ih _ (fun d hd => ha d (by simp [hd]))
    exact mulCoeffLists_width p _ cs (translateBits_width p a g (ha a (by simp)))
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]
/-- The loop computes precisely the product of the specified translated polynomials. -/
theorem coeffPolynomial_fold_normStep (z : R) (pre : List BitStr) (p g : BitStr) (cs : List BitStr)
    (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) (ha : ∀ a ∈ pre, a.length = p.length) :
    coeffPolynomial z (pre.foldl normStep (p, g, cs)).2.2 =
      (pre.map (fun a => translatedPolynomial (polyOfBits g) (evalBits z a))).prod * coeffPolynomial z cs := by
  induction pre generalizing cs with
  | nil => simp
  | cons a pre ih =>
    have ha₀ := ha a (by simp)
    change coeffPolynomial z (pre.foldl normStep (p, g, mulCoeffLists p (translateBits p a g) cs)).2.2 = _
    rw [ih _ (fun d hd => ha d (by simp [hd])),
      coeffPolynomial_mulCoeffLists z p _ cs hz (translateBits_width p a g ha₀),
      coeffPolynomial_translateBits z p a g hp hz ha₀]
    simp only [List.map_cons, List.prod_cons, translatedPolynomial]
    ring
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]
/-- The printed coefficient list represents the prescribed translate product. -/
theorem coeffPolynomial_normProductBits (z : R) (p g : BitStr) (as : List BitStr)
    (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) (ha : ∀ a ∈ as, a.length = p.length) :
    coeffPolynomial z (normProductBits p g as) =
      (as.map (fun a => translatedPolynomial (polyOfBits g) (evalBits z a))).prod := by
  rw [normProductBits, coeffPolynomial_fold_normStep z as p g _ hp hz ha]
  simp [evalBits_oneBits z p hp]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R] [CharP R 2] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R] in
theorem evalBits_rootBits (z : R) (p : BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) :
    evalBits z (rootBits p) = z := by
  rw [rootBits, evalBits_shiftReduce z p _ (length_oneBits p) hz, evalBits_oneBits z p hp, mul_one]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial Polynomial BinaryFiniteField
variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]
include hf in
/-- The canonical root's Frobenius orbit closes at the degree of its modulus. -/
theorem root_frobenius_period : AdjoinRoot.root f ^ (2 ^ f.natDegree) = AdjoinRoot.root f := by
  have hi := AdjoinRoot.isIntegral_root hf.ne_zero
  have hm : minpoly (ZMod 2) (AdjoinRoot.root f) = f := by
    simpa only [hf.leadingCoeff, inv_one, map_one, mul_one] using AdjoinRoot.minpoly_root hf.ne_zero
  apply (minpoly_natDegree_dvd_iff_frobenius _ hi _).mp
  rw [hm]
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost BinaryPolynomial Polynomial BinaryFiniteField
variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]
include hf in
theorem _root_.solution (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic) :
    (polyOfBits (composedSumBits p g)).map (algebraMap (ZMod 2) (AdjoinRoot f)) =
      composedSumPolynomial (polyOfBits g) (AdjoinRoot.root f) f.natDegree := by
  let : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have hp0 : p ≠ [] := by
    intro h
    have hpos := (Fact.out : Irreducible f).natDegree_pos
    simp [h] at hp
    omega
  let bs := orbitBits (unary p.length) p (rootBits p)
  let cs := normProductBits p g bs
  have hb : ∀ a ∈ bs, a.length = p.length := orbitBits_width _ p _ (length_rootBits p)
  have hc : ∀ c ∈ cs, c.length = p.length := by
    apply fold_normStep_width bs p g [oneBits p] hb
    intro c h
    obtain rfl := List.mem_singleton.mp h
    exact length_oneBits p
  have hroot := root_eq f p hpoly
  have he := map_evalBits_orbitBits (AdjoinRoot.root f) (unary p.length) p (rootBits p)
    hroot (length_rootBits p)
  rw [evalBits_rootBits _ p hp0 hroot, length_unary, hp] at he
  have hprod : coeffPolynomial (AdjoinRoot.root f) cs =
      composedSumPolynomial (polyOfBits g) (AdjoinRoot.root f) f.natDegree := by
    dsimp only [cs]
    rw [coeffPolynomial_normProductBits _ p g bs hp0 hroot hb]
    have h := congrArg (fun l : List (AdjoinRoot f) =>
      (l.map (translatedPolynomial (polyOfBits g))).prod) he
    simpa only [List.map_map, List.map_ofFn, Function.comp_def, bs, hp, composedSumPolynomial] using h
  change (polyOfBits (descendBits cs)).map _ = _
  rw [map_polyOfBits_descendBits _ cs ?_, hprod]
  intro c hmem
  apply evalBits_eq_head_of_zero_or_one f hf p c hp ((hc c hmem).trans hp) hp0
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
  have hcoeff : (coeffPolynomial (AdjoinRoot.root f) cs).coeff i = evalBits (AdjoinRoot.root f) c := by
    simp only [coeff_coeffPolynomial, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some, he]
  rw [← hcoeff, hprod]
  exact composedSumPolynomial_coeff_zero_or_one _ hg _ _ (root_frobenius_period f hf) i
end MIPRE.LowDegree.BinaryQuotient
