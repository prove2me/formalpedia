-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.map_orbitPolynomialBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:25.235493+00:00
-- url     : https://prove2.me/submissions/8d0ffce0-d81a-4a7f-8d22-118fe63218c0

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryOrbitDescent.lean (solution of MIPRE.LowDegree.BinaryQuotient.map_orbitPolynomialBits);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_coeffPolynomial_linearMulCarry
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_evalBits_eq_head_of_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_linearMulCarry_width
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
/-- Multiplication by a linear factor is correct in any represented binary algebra. -/
theorem coeffPolynomial_linearMulBits [CharP R 2] (z : R) (p a : BitStr)
    (cs : List BitStr) (hz : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hs : ∀ c ∈ cs, c.length = p.length) :
    coeffPolynomial z (linearMulBits p a cs) =
      (X + C (evalBits z a)) * coeffPolynomial z cs := by
  rw [linearMulBits, coeffPolynomial_linearMulCarry z p a _ cs hz ha (length_zeroBits p) hs,
    evalBits_zeroBits, map_zero, zero_add]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Valid fixed-width coefficients remain valid through the product loop. -/
theorem fold_productStep_width_eq (bs : List BitStr) (p : BitStr) (cs : List BitStr)
    (hb : ∀ a ∈ bs, a.length = p.length) (hs : ∀ c ∈ cs, c.length = p.length) :
    ∀ c ∈ (bs.foldl productStep (p, cs)).2, c.length = p.length := by
  induction bs generalizing cs with
  | nil => exact hs
  | cons a bs ih =>
    apply ih (linearMulBits p a cs) (fun b hb' => hb b (by simp [hb']))
    exact linearMulCarry_width p a _ cs (hb a (by simp)) (length_zeroBits p) hs
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- The accumulated coefficient polynomial is the product of all supplied factors. -/
theorem coeffPolynomial_fold_productStep [CharP R 2] (z : R) (p : BitStr)
    (bs cs : List BitStr) (hz : z ^ p.length = evalBits z p)
    (hb : ∀ a ∈ bs, a.length = p.length) (hs : ∀ c ∈ cs, c.length = p.length) :
    coeffPolynomial z (bs.foldl productStep (p, cs)).2 =
      (bs.map (fun a => X + C (evalBits z a))).prod * coeffPolynomial z cs := by
  induction bs generalizing cs with
  | nil => simp
  | cons a bs ih =>
    have ha := hb a (by simp)
    have ht : ∀ b ∈ bs, b.length = p.length := fun b hb' => hb b (by simp [hb'])
    have hc := linearMulCarry_width p a (zeroBits p) cs ha (length_zeroBits p) hs
    change coeffPolynomial z (bs.foldl productStep (p, linearMulBits p a cs)).2 = _
    rw [ih (linearMulBits p a cs) ht hc, coeffPolynomial_linearMulBits z p a cs hz ha hs]
    simp only [List.map_cons, List.prod_cons]
    ring
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- The encoded product has the expected polynomial semantics. -/
theorem coeffPolynomial_linearProductBits [CharP R 2] (z : R) (p : BitStr)
    (bs : List BitStr) (hp : p ≠ []) (hz : z ^ p.length = evalBits z p)
    (hb : ∀ a ∈ bs, a.length = p.length) :
    coeffPolynomial z (linearProductBits p bs) =
      (bs.map (fun a => X + C (evalBits z a))).prod := by
  rw [linearProductBits, coeffPolynomial_fold_productStep z p bs [oneBits p] hz hb
    (by intro c hc; obtain rfl := List.mem_singleton.mp hc; exact length_oneBits p)]
  simp [evalBits_oneBits z p hp]
end
end MIPRE.LowDegree.BinaryQuotient

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
/-- The printed product equals the product of the Frobenius conjugate linear factors. -/
theorem coeffPolynomial_orbitProductBits [CharP R 2] (z : R) (u : Unary) (p a : BitStr)
    (hp : p ≠ []) (hz : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    coeffPolynomial z (orbitProductBits u p a) =
      (List.ofFn (fun i : Fin u.length => X + C (evalBits z a ^ (2 ^ (i : ℕ))))).prod := by
  rw [orbitProductBits, coeffPolynomial_linearProductBits z p _ hp hz (orbitBits_width u p a ha)]
  have h := congrArg (fun l : List R => (l.map (fun x => X + C x)).prod)
    (map_evalBits_orbitBits z u p a hz ha)
  simpa only [List.map_map, List.map_ofFn, Function.comp_def] using h
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
/-- Every printed coefficient has the prescribed quotient width. -/
theorem orbitProductBits_width (u : Unary) (p a : BitStr) (ha : a.length = p.length) :
    ∀ c ∈ orbitProductBits u p a, c.length = p.length := by
  apply fold_productStep_width_eq _ p [oneBits p] (orbitBits_width u p a ha)
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact length_oneBits p
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R]
/-- Splitting off the last conjugate gives the other endpoint of the same product. -/
theorem orbitPolynomial_succ' (x : R) (n : ℕ) :
    orbitPolynomial x (n + 1) = orbitPolynomial x n * (X + C (x ^ (2 ^ n))) := by
  rw [orbitPolynomial, List.ofFn_succ', List.prod_concat]
  rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R]
/-- Applying Frobenius to coefficients shifts the starting element by one conjugate. -/
theorem map_frobenius_orbitPolynomial [CharP R 2] (x : R) (n : ℕ) :
    (orbitPolynomial x n).map (frobenius R 2) = orbitPolynomial (x ^ 2) n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [orbitPolynomial_succ, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_X, Polynomial.map_C, frobenius_def, ih, orbitPolynomial_succ]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R]
/-- A closed orbit gives a polynomial fixed by coefficient Frobenius. -/
theorem map_frobenius_orbitPolynomial_of_closed [IsDomain R] [CharP R 2]
    (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) :
    (orbitPolynomial x n).map (frobenius R 2) = orbitPolynomial x n := by
  rw [map_frobenius_orbitPolynomial]
  apply mul_left_cancel₀ (monic_X_add_C x).ne_zero
  rw [← orbitPolynomial_succ, orbitPolynomial_succ', hx, mul_comm]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R]
/-- Coefficients of a closed binary orbit polynomial belong to the prime field. -/
theorem orbitPolynomial_coeff_zero_or_one [IsDomain R] [CharP R 2]
    (x : R) (n : ℕ) (hx : x ^ (2 ^ n) = x) (i : ℕ) :
    (orbitPolynomial x n).coeff i = 0 ∨ (orbitPolynomial x n).coeff i = 1 := by
  have h := congrArg (fun p : Polynomial R => p.coeff i)
    (map_frobenius_orbitPolynomial_of_closed x n hx)
  rw [coeff_map, frobenius_def] at h
  have hz : (orbitPolynomial x n).coeff i * ((orbitPolynomial x n).coeff i - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun BinaryPolynomial Polynomial
variable {R : Type*} [CommRing R]
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
include hf in
theorem _root_.solution [Fact (Irreducible f)] (u : Unary) (p a : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (hp0 : p ≠ []) (ha : a.length = p.length)
    (hclosed : evalBits (AdjoinRoot.root f) a ^ (2 ^ u.length) =
      evalBits (AdjoinRoot.root f) a) :
    (polyOfBits (orbitPolynomialBits u p a)).map (algebraMap (ZMod 2) (AdjoinRoot f)) =
      orbitPolynomial (evalBits (AdjoinRoot.root f) a) u.length := by
  let : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  have hprod : coeffPolynomial (AdjoinRoot.root f) (orbitProductBits u p a) =
      orbitPolynomial (evalBits (AdjoinRoot.root f) a) u.length :=
    coeffPolynomial_orbitProductBits _ u p a hp0 (root_eq f p hpoly) ha
  rw [orbitPolynomialBits, map_polyOfBits_descendBits _ _ ?_, hprod]
  intro c hc
  apply evalBits_eq_head_of_zero_or_one f hf p c hp
    ((orbitProductBits_width u p a ha c hc).trans hp) hp0
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
  have hcoeff : (coeffPolynomial (AdjoinRoot.root f) (orbitProductBits u p a)).coeff i =
      evalBits (AdjoinRoot.root f) c := by
    simp only [coeff_coeffPolynomial, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he]
  rw [← hcoeff, hprod]
  exact orbitPolynomial_coeff_zero_or_one _ _ hclosed i
end MIPRE.LowDegree.BinaryQuotient
