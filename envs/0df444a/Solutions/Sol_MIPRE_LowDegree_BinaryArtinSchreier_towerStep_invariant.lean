-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryArtinSchreier.towerStep_invariant
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:11:27.419879+00:00
-- url     : https://prove2.me/submissions/92f38ad7-ea69-4f9c-bead-a3bf90a28c3b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryArtinSchreierTower.lean (solution of MIPRE.LowDegree.BinaryArtinSchreier.towerStep_invariant);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_towerStepBits_cubic
import Theorems.Thm_MIPRE_LowDegree_BinaryArtinSchreier_towerStepBits_monic_natDegree
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_natDegree_polyOfBits_append_true

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
/-- A nonempty normalized list has a leading coefficient equal to one. -/
theorem normalizeBits_getLast (a : BitStr) :
    normalizeBits a = [] ∨ (normalizeBits a).getLastD false = true := by
  induction a with
  | nil => exact Or.inl rfl
  | cons b a ih =>
    rcases ih with h | h
    · cases b <;> simp [normalizeBits_cons, normalizeStep, h]
    · have hn : normalizeBits a ≠ [] := by intro he; simp [he] at h
      cases ha : normalizeBits a with
      | nil => exact (hn ha).elim
      | cons c a =>
        cases b <;> simpa [normalizeBits_cons, normalizeStep, ha, List.getLastD_cons] using h
end
end MIPRE.LowDegree.BinaryPolynomial

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
/-- Normalization leaves a true leading bit on every valid step output. -/
theorem towerStepBits_getLast (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (hp : p ≠ []) :
    (towerStepBits p).getLastD false = true := by
  have hm := (towerStepBits_monic_natDegree p hp).1
  rcases normalizeBits_getLast
    ((parameterOrbitBits p).foldr (fun b s => artinSchreierStep s b) []) with h | h
  · have he : towerStepBits p = [] := h
    exact (hm.ne_zero (by rw [he]; rfl)).elim
  · exact h
end
end MIPRE.LowDegree.BinaryArtinSchreier

namespace MIPRE.LowDegree.BinaryArtinSchreier
noncomputable section
open Cost Cost.PolyTimeFun BinaryPolynomial BinaryQuotient Polynomial
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFintype
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientFiniteDimensional
attribute [local instance] MIPRE.LowDegree.BinaryArtinSchreier.quotientCharP
/-- A valid step has doubled lower-coefficient width. -/
theorem towerStepBits_length (p : BitStr)
    [Fact (Irreducible (polyOfBits (p ++ [true])))] (hp : p ≠ []) :
    (towerStepBits p).length = 2 * p.length + 1 := by
  rw [← natDegree_add_one_of_getLast _ (towerStepBits_getLast p hp),
    (towerStepBits_monic_natDegree p hp).2]
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
theorem _root_.solution (p : BitStr) (t : ℕ) (h : TowerInvariant p t) :
    TowerInvariant (towerStepBits p).dropLast (t + 1) := by
  let : Fact (Irreducible (polyOfBits (p ++ [true]))) := ⟨h.irreducible⟩
  have hp : p ≠ [] := List.length_pos_iff.mp (by rw [h.width]; positivity)
  have he : (towerStepBits p).dropLast ++ [true] = towerStepBits p :=
    dropLast_append_true _ (towerStepBits_getLast p hp)
  have hi := towerStepBits_irreducible p (t + 1) h.width h.cubic
  refine ⟨?_, he.symm ▸ hi, ?_⟩
  · rw [List.length_dropLast, towerStepBits_length p hp, Nat.add_sub_cancel, h.width,
      pow_succ]
    simp only [pow_succ]
    ring
  · exact cubic_irreducible_congr (congrArg polyOfBits he) (he.symm ▸ hi) hi
      (towerStepBits_cubic p (t + 1) h.width h.cubic)
end MIPRE.LowDegree.BinaryArtinSchreier
