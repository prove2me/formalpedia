-- Prove2me | solution 1 for MIPRE.LowDegree.decidesComponent_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:23:28.498523+00:00
-- url     : https://prove2.me/submissions/69331126-1acb-4fc6-8806-605ca519b53c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/IdempotentSplit.lean (solution of MIPRE.LowDegree.decidesComponent_of_mem_span);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
variable {R : Type*} [CommRing R] [DecidableEq R]
variable [Algebra (ZMod 2) R]
attribute [local instance] MIPRE.LowDegree.instFactPrimeOfNatNat_mIPRE
theorem _root_.solution (e : R) (bs : List R)
    (hb : ∀ b ∈ bs, DecidesComponent e b) (z : R)
    (hz : z ∈ Submodule.span (ZMod 2) {b | b ∈ bs}) : DecidesComponent e z := by
  let L : R →ₗ[ZMod 2] R :=
    { toFun := fun x => e * x
      map_add' := fun x y => mul_add e x y
      map_smul' := fun c x => by simp only [RingHom.id_apply, mul_smul_comm] }
  have hs : Submodule.span (ZMod 2) {b | b ∈ bs} ≤
      (Submodule.span (ZMod 2) ({e} : Set R)).comap L := by
    apply Submodule.span_le.mpr
    intro b hbmem
    change e * b ∈ Submodule.span (ZMod 2) ({e} : Set R)
    rcases hb b hbmem with h | h
    · rw [h]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.subset_span (Set.mem_singleton e)
  have hm : e * z ∈ Submodule.span (ZMod 2) ({e} : Set R) := hs hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  rcases BinaryLinear.binary_eq_zero_or_one c with rfl | rfl
  · left
    simpa only [zero_smul] using hc.symm
  · right
    simpa only [one_smul] using hc.symm
end MIPRE.LowDegree
