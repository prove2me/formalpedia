-- Prove2me | solution 1 for MIPRE.LowDegree.ComponentFamily.split
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:23:27.968216+00:00
-- url     : https://prove2.me/submissions/948df171-ffb4-47c3-94a8-23bdb8350cf9

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/IdempotentSplit.lean (solution of MIPRE.LowDegree.ComponentFamily.split);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem mem_splitComponent (e b x : R) :
    x ∈ splitComponent e b ↔ (x = e * b ∨ x = e * (1 - b)) ∧ x ≠ 0 := by
  simp [splitComponent, and_comm]
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_sum (e b : R) : (splitComponent e b).sum = e := by
  have h : e * b + e * (1 - b) = e := by ring
  by_cases h₁ : e * b = 0 <;> by_cases h₂ : e * (1 - b) = 0 <;>
    simp [splitComponent, h₁, h₂] at h ⊢ <;> exact h
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_factor {e b x : R} (hx : x ∈ splitComponent e b) :
    ∃ c, x = e * c := by
  rcases (mem_splitComponent e b x).mp hx with ⟨h | h, _⟩
  · exact ⟨b, h⟩
  · exact ⟨1 - b, h⟩
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem one_sub_idempotent {b : R} (hb : b * b = b) : (1 - b) * (1 - b) = 1 - b := by
  calc
    (1 - b) * (1 - b) = 1 - b - b + b * b := by ring
    _ = 1 - b := by rw [hb]; ring
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem mul_idempotent {e b : R} (he : e * e = e) (hb : b * b = b) :
    (e * b) * (e * b) = e * b := by
  calc
    (e * b) * (e * b) = (e * e) * (b * b) := by ring
    _ = e * b := by rw [he, hb]
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_idempotent {e b : R} (he : e * e = e) (hb : b * b = b)
    {x : R} (hx : x ∈ splitComponent e b) : x * x = x := by
  rcases (mem_splitComponent e b x).mp hx with ⟨rfl | rfl, _⟩
  · exact mul_idempotent he hb
  · exact mul_idempotent he (one_sub_idempotent hb)
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem splitComponent_pairwise (e : R) {b : R} (hb : b * b = b) :
    (splitComponent e b).Pairwise (fun x y => x * y = 0) := by
  apply List.Pairwise.filter
  have hc : (e * b) * (e * (1 - b)) = 0 := by
    calc
      (e * b) * (e * (1 - b)) = (e * e) * (b - b * b) := by ring
      _ = 0 := by rw [hb, sub_self, mul_zero]
  simp [hc]
end
end MIPRE.LowDegree

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.ComponentFamily
variable {R : Type*} [CommRing R] [DecidableEq R]
theorem _root_.solution {l : List R} (hl : ComponentFamily l) {b : R} (hb : b * b = b) :
    ComponentFamily (splitComponents l b) := by
  constructor
  · intro x hx
    obtain ⟨e, _, hx⟩ := List.mem_flatMap.mp hx
    exact ((mem_splitComponent e b x).mp hx).2
  · intro x hx
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    exact splitComponent_idempotent (hl.idempotent e he) hb hx
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun e _ => splitComponent_pairwise e hb, hl.orthogonal.imp ?_⟩
    intro e f hef x hx y hy
    obtain ⟨c, rfl⟩ := splitComponent_factor hx
    obtain ⟨d, rfl⟩ := splitComponent_factor hy
    calc
      (e * c) * (f * d) = (e * f) * (c * d) := by ring
      _ = 0 := by rw [hef, zero_mul]
  · have hs (l : List R) : (splitComponents l b).sum = l.sum := by
      induction l with
      | nil => rfl
      | cons e l ih =>
        simpa only [splitComponents, List.flatMap_cons, List.sum_append,
          splitComponent_sum, List.sum_cons] using congrArg (fun x => e + x) ih
    exact (hs l).trans hl.sum_eq_one
end MIPRE.LowDegree.ComponentFamily
