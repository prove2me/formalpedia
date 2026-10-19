-- Prove2me | solution 1 for MIPRE.SeededGame.sum_failAt_four_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:10.398697+00:00
-- url     : https://prove2.me/submissions/bc72a97f-d9ac-44d0-ae82-a6dc7790a4ad

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.SeededGame.sum_failAt_four_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Theorems.Thm_MIPRE_SeededGame_sum_oDist_mul
import Theorems.Thm_MIPRE_TensorProductStrategy_failAt_nonneg

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SeededGame
section
open Finset Matrix
variable {A : Type*} [Inhabited A]
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
omit [DecidableEq V] [Nonempty V] [Inhabited A] in
theorem card_role_prod_prod : (Fintype.card (Role × Role × V) : ℝ) = 9 * Fintype.card V := by
  rw [Fintype.card_prod, Fintype.card_prod, show Fintype.card Role = 3 from rfl]
  push_cast
  ring
end
end MIPRE.SeededGame

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- The value is the `μ`-average of the conditional success probability. -/
theorem value_eq_sum_succAt (S : TensorProductStrategy G) :
    S.value = ∑ x, ∑ y, G.μ x y * S.succAt x y := by
  unfold value succAt
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [born]; ring
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt (S : TensorProductStrategy G) :
    1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y := by
  have hsplit : ∑ x, ∑ y, G.μ x y * S.failAt x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * S.succAt x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by simp only [failAt]; ring
  rw [hsplit, G.μ_sum_one, value_eq_sum_succAt]
end
end MIPRE.TensorProductStrategy

namespace MIPRE
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
/-- A sum over the three roles. -/
theorem Role.sum_eq {M : Type*} [AddCommMonoid M] (f : Role → M) :
    ∑ r, f r = f .oracle + f .alice + f .bob := by
  change ∑ r ∈ ({Role.oracle, Role.alice, Role.bob} : Finset Role), f r = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SeededGame
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
omit [Inhabited A] in
theorem _root_.solution (N : TensorProductStrategy S.oracular.toGame) :
    (Fintype.card V : ℝ)⁻¹ * ∑ z, (N.failAt (Role.oracle, z) (Role.oracle, z)
        + (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z)))
      ≤ 9 * (1 - N.value) := by
  set g : Role × Role × V → ℝ :=
    fun s => N.failAt (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => N.failAt_nonneg _ _
  have htot : 1 - N.value = (Fintype.card (Role × Role × V) : ℝ)⁻¹ * ∑ s, g s := by
    rw [N.one_sub_value_eq_sum_failAt]
    exact S.sum_oDist_mul N.failAt
  have hsplit : ∑ s, g s = ∑ r₁ : Role, ∑ r₂ : Role, ∑ z : V, g (r₁, r₂, z) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r₁ _ => Fintype.sum_prod_type _
  have hpos : ∀ r₁ r₂ : Role, 0 ≤ ∑ z : V, g (r₁, r₂, z) := fun r₁ r₂ =>
    Finset.sum_nonneg fun z _ => hg0 _
  have hfour : ∑ z, (N.failAt (Role.oracle, z) (Role.oracle, z)
        + (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z)))
      = ∑ z, g (.oracle, .oracle, z) + (∑ z, g (.alice, .alice, z)
          + ∑ z, g (.oracle, .alice, z) + ∑ z, g (.oracle, .bob, z)) := by
    simp only [← Finset.sum_add_distrib]
    rfl
  have hle : ∑ z, (N.failAt (Role.oracle, z) (Role.oracle, z)
        + (N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
          + N.failAt (Role.oracle, z) (Role.bob, S.LB z))) ≤ ∑ s, g s := by
    rw [hfour, hsplit]
    simp only [Role.sum_eq]
    linarith [hpos .alice .oracle, hpos .alice .bob, hpos .bob .oracle, hpos .bob .alice,
      hpos .bob .bob]
  have hcard : (Fintype.card V : ℝ)⁻¹ = 9 * (Fintype.card (Role × Role × V) : ℝ)⁻¹ := by
    have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    rw [card_role_prod_prod (V := V)]
    field_simp
  rw [htot, hcard, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hle (by positivity)) (by norm_num)
end MIPRE.SeededGame
