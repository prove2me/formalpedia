-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:13.435522+00:00
-- url     : https://prove2.me/submissions/1ff5eec7-bc2c-4781-8498-e4f7a9599d44

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryComposedSum.lean (solution of MIPRE.LowDegree.BinaryQuotient.composedSumBits_correct);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryFiniteField_minpoly_natDegree_add_of_coprime
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_map_composedSumBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
/-- A nonempty translate product vanishes at the sum of the translating element and any root. -/
theorem eval_composedSumPolynomial [CharP R 2]
    (g : Polynomial (ZMod 2)) (x y : R) (n : ℕ) (hn : 0 < n) (hy : aeval y g = 0) :
    (composedSumPolynomial g x n).eval (x + y) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [composedSumPolynomial_succ, eval_mul]
  have h : (translatedPolynomial g x).eval (x + y) = 0 := by
    rw [translatedPolynomial, eval_comp, eval_add, eval_X, eval_C]
    have he : x + y + x = y := by
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    rw [he, eval_map, ← aeval_def]
    exact hy
  rw [h, zero_mul]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
variable {S : Type*} [CommRing S] [Algebra (ZMod 2) S]
/-- Translation commutes with an algebra embedding of the coefficient field. -/
theorem map_translatedPolynomial (φ : R →ₐ[ZMod 2] S) (g : Polynomial (ZMod 2)) (x : R) :
    (translatedPolynomial g x).map φ.toRingHom = translatedPolynomial g (φ x) := by
  have hbase : φ.toRingHom.comp (algebraMap (ZMod 2) R) = algebraMap (ZMod 2) S := by
    ext z
    exact φ.commutes z
  rw [translatedPolynomial, Polynomial.map_comp, Polynomial.map_map, hbase,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Polynomial
variable {R : Type*} [CommRing R] [Algebra (ZMod 2) R]
variable {S : Type*} [CommRing S] [Algebra (ZMod 2) S]
/-- The composed-sum product commutes with coefficient-field embeddings. -/
theorem map_composedSumPolynomial (φ : R →ₐ[ZMod 2] S) (g : Polynomial (ZMod 2)) (x : R) (n : ℕ) :
    (composedSumPolynomial g x n).map φ.toRingHom = composedSumPolynomial g (φ x) n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [composedSumPolynomial_succ, Polynomial.map_mul, map_translatedPolynomial, ih,
      map_pow, composedSumPolynomial_succ]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial Polynomial BinaryFiniteField
variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]
include hf in
/-- The descended composed sum is monic, of the product degree. -/
theorem composedSumBits_monic_natDegree (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic) :
    (polyOfBits (composedSumBits p g)).Monic ∧
      (polyOfBits (composedSumBits p g)).natDegree = f.natDegree * (polyOfBits g).natDegree := by
  have h := map_composedSumBits f hf p g hp hpoly hg
  constructor
  · have hm := composedSumPolynomial_monic (polyOfBits g) hg (AdjoinRoot.root f) f.natDegree
    rw [← h] at hm
    exact Polynomial.monic_map_iff.mp hm
  · rw [← natDegree_map_eq_of_injective (algebraMap (ZMod 2) (AdjoinRoot f)).injective, h,
      natDegree_composedSumPolynomial _ hg]
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost BinaryPolynomial Polynomial BinaryFiniteField
variable (f : Polynomial (ZMod 2)) (hf : f.Monic) [Fact (Irreducible f)]
include hf in
theorem _root_.solution (p g : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (hg : (polyOfBits g).Monic)
    (hgi : Irreducible (polyOfBits g)) (hcop : f.natDegree.Coprime (polyOfBits g).natDegree) :
    (polyOfBits (composedSumBits p g)).Monic ∧ Irreducible (polyOfBits (composedSumBits p g)) ∧
      (polyOfBits (composedSumBits p g)).natDegree = f.natDegree * (polyOfBits g).natDegree := by
  let L := AlgebraicClosure (ZMod 2)
  let : CharP L 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) L).injective 2
  have hfi : Irreducible f := Fact.out
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero L f hfi.degree_pos.ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero L (polyOfBits g) hgi.degree_pos.ne'
  let φ : AdjoinRoot f →ₐ[ZMod 2] L := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) x hx
  have hφ : φ (AdjoinRoot.root f) = x := AdjoinRoot.liftAlgHom_root ..
  have hbase : φ.toRingHom.comp (algebraMap (ZMod 2) (AdjoinRoot f)) = algebraMap (ZMod 2) L := by
    ext z
    exact φ.commutes z
  have hmap := congrArg (Polynomial.map φ.toRingHom) (map_composedSumBits f hf p g hp hpoly hg)
  rw [Polynomial.map_map, hbase, map_composedSumPolynomial, hφ] at hmap
  have hz : aeval (x + y) (polyOfBits (composedSumBits p g)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hmap]
    exact eval_composedSumPolynomial _ x y _ hfi.natDegree_pos hy
  have hmd := composedSumBits_monic_natDegree f hf p g hp hpoly hg
  have hix : IsIntegral (ZMod 2) x := ⟨f, hf, hx⟩
  have hiy : IsIntegral (ZMod 2) y := ⟨_, hg, hy⟩
  have hmx : minpoly (ZMod 2) x = f := (minpoly.eq_of_irreducible_of_monic hfi hx hf).symm
  have hmy : minpoly (ZMod 2) y = polyOfBits g := (minpoly.eq_of_irreducible_of_monic hgi hy hg).symm
  have hdeg : (minpoly (ZMod 2) (x + y)).natDegree = f.natDegree * (polyOfBits g).natDegree := by
    rw [minpoly_natDegree_add_of_coprime x y hix hiy (by simpa only [hmx, hmy] using hcop), hmx, hmy]
  have heq : polyOfBits (composedSumBits p g) = minpoly (ZMod 2) (x + y) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hix.add hiy)) hmd.1
      (minpoly.dvd _ _ hz) (by rw [hmd.2, hdeg])
  refine ⟨hmd.1, ?_, hmd.2⟩
  rw [heq]
  exact minpoly.irreducible (hix.add hiy)
end MIPRE.LowDegree.BinaryQuotient
