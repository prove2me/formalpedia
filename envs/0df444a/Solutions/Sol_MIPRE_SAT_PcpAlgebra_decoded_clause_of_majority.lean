-- Prove2me | solution 1 for MIPRE.SAT.PcpAlgebra.decoded_clause_of_majority
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:35.608589+00:00
-- url     : https://prove2.me/submissions/4a7df70d-cb97-439a-883d-070140bfe664

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpBlocks.lean (solution of MIPRE.SAT.PcpAlgebra.decoded_clause_of_majority);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Theorems.Thm_MIPRE_LowDegree_eq_of_majority_agree
import Theorems.Thm_MIPRE_SAT_PcpAlgebra_degreeOf_constraint_le
import Theorems.Thm_MIPRE_SAT_PcpAlgebra_degreeOf_zeroCombination_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
variable [DecidableEq F]
/-- Decoding preserves a polynomial evaluation that already equals a Boolean value. -/
theorem coded_eq_of_eval_eq_ofBool (g : MvPolynomial (Fin m) F) (y : Fin m → Bool)
    (b : Bool) (h : eval (pt y) g = ofBool b) : coded g y = ofBool b := by
  cases b <;> simp [coded, codedOn, h, ofBool]
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
/-- A verifier may impose other tests as well: agreement on any accepted set larger
than half the field cube already forces the same identity. -/
theorem eq_of_majority_subset {f g : MvPolynomial (Fin m) F} {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d)
    (hsize : 2 * (m * d) ≤ Fintype.card F) (S : Finset (Fin m → F))
    (hS : ∀ x ∈ S, eval x f = eval x g)
    (hmajority : Fintype.card F ^ m < 2 * S.card) : f = g := by
  apply eq_of_majority_agree hf hg hsize
  apply hmajority.trans_le
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro x hx
  exact mem_agree.mpr (hS x hx)
end
end MIPRE.LowDegree

namespace MIPRE.SAT.PcpAlgebra
noncomputable section
open Finset MvPolynomial LowDegree
variable {F : Type*} [Field F] {m : ℕ}
/-- Soundness first forces both tested polynomial identities. -/
theorem identities_of_majority [Fintype F] [DecidableEq F]
    (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c₀ : MvPolynomial (Fin m) F)
    (c : Fin m → MvPolynomial (Fin m) F) {d : ℕ}
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ d)
    (hc₀ : ∀ j, c₀.degreeOf j ≤ d) (hc : ∀ i j, (c i).degreeOf j ≤ d)
    (hq : 2 * (m * (6 + 5 * max d 1)) ≤ Fintype.card F)
    (S : Finset (Fin m → F)) (hS : ∀ z ∈ S, Accepts φ g sign c₀ c z)
    (hmajority : Fintype.card F ^ m < 2 * S.card) :
    c₀ = constraint φ g sign ∧ c₀ = zeroCombination c := by
  have hd : d ≤ 6 + 5 * max d 1 := by have := le_max_left d 1; omega
  have hd' : d + 2 ≤ 6 + 5 * max d 1 := by have := le_max_left d 1; omega
  constructor
  · exact eq_of_majority_subset (fun j => (hc₀ j).trans hd)
      (degreeOf_constraint_le φ g sign hφ hg) hq S (fun z hz => (hS z hz).1) hmajority
  · exact eq_of_majority_subset (fun j => (hc₀ j).trans hd)
      (fun j => (degreeOf_zeroCombination_le c hc j).trans hd') hq S
      (fun z hz => (hS z hz).2) hmajority
end
end MIPRE.SAT.PcpAlgebra

namespace MIPRE.SAT.PcpAlgebra
noncomputable section
open Finset MvPolynomial LowDegree
variable {F : Type*} [Field F] {m : ℕ}
/-- On every described Boolean clause, an identity certificate forces one answer
polynomial to match its sign. This is the clause-satisfaction step of decoding. -/
theorem clause_satisfied_of_identities
    (φ : MvPolynomial (Fin m) F) (g : Fin 5 → MvPolynomial (Fin m) F)
    (sign : Fin 5 → Fin m) (c : Fin m → MvPolynomial (Fin m) F)
    (h : constraint φ g sign = zeroCombination c) (y : Fin m → Bool)
    (hφ : eval (pt y) φ = 1) :
    ∃ i : Fin 5, eval (pt y) (g i) = ofBool (y (sign i)) := by
  have hz : eval (pt y) (constraint φ g sign) = 0 := by rw [h]; simp
  simp only [constraint, map_mul, map_prod, map_sub, eval_X, hφ, one_mul] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  exact ⟨i, sub_eq_zero.mp hi⟩
end
end MIPRE.SAT.PcpAlgebra

namespace MIPRE.SAT.PcpParams
noncomputable section
open Finset MvPolynomial LowDegree
theorem blockIndex_injective (P : PcpParams) (i : Fin 5) :
    Function.Injective (P.blockIndex i) := by
  intro j k h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [blockIndex] at this
  omega
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpAlgebra
noncomputable section
open Finset MvPolynomial LowDegree
variable {P : PcpParams} {F : Type*} [Field F]
theorem degreeOf_liftAnswer_le (i : Fin 5) (g : MvPolynomial (Fin P.m) F)
    {d : ℕ} (hg : ∀ j, g.degreeOf j ≤ d) (j : Fin P.m') :
    (liftAnswer i g).degreeOf j ≤ d := by
  by_cases h : ∃ k, P.blockIndex i k = j
  · obtain ⟨k, rfl⟩ := h
    rw [liftAnswer, degreeOf_rename_of_injective (P.blockIndex_injective i)]
    exact hg k
  · have hz : (liftAnswer i g).degreeOf j = 0 := by
      by_contra hn
      obtain ⟨k, _, hk⟩ := mem_vars_rename _ g (mem_vars_iff_degreeOf_ne_zero.mpr hn)
      exact h ⟨k, hk⟩
    rw [hz]
    exact Nat.zero_le _
end
end MIPRE.SAT.PcpAlgebra

namespace MIPRE.SAT.PcpAlgebra
noncomputable section
open Finset MvPolynomial LowDegree
variable {P : PcpParams} {F : Type*} [Field F]
/-- The typed tests on a proof's evaluations are exactly the polynomial tests. -/
theorem typedAccepts_ev_iff (φ : MvPolynomial (Fin P.m') F) (pf : PcpProof P F)
    (z : Fin P.m' → F) :
    TypedAccepts φ z (pf.ev z) ↔
      Accepts φ (fun i => liftAnswer i (pf.g i)) P.signIndex (pf.c 0)
        (fun j => pf.c j.succ) z := by
  simp [TypedAccepts, Accepts, constraint, zeroCombination, cubeZero, PcpProof.ev]
end
end MIPRE.SAT.PcpAlgebra

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpAlgebra
open Finset MvPolynomial LowDegree
variable {P : PcpParams} {F : Type*} [Field F]
theorem _root_.solution [Fintype F] [DecidableEq F]
    (φ : MvPolynomial (Fin P.m') F) (hφ : ∀ j, φ.degreeOf j ≤ 6)
    (pf : PcpProof P F) (hq : 82 * P.m' ≤ Fintype.card F)
    (S : Finset (Fin P.m' → F)) (hS : ∀ z ∈ S, TypedAccepts φ z (pf.ev z))
    (hmajority : Fintype.card F ^ P.m' < 2 * S.card)
    (y : Fin P.m' → Bool) (hy : eval (pt y) φ = 1) :
    ∃ i : Fin 5, coded (pf.g i) (P.block i y) = ofBool (y (P.signIndex i)) := by
  obtain ⟨h₀, h₁⟩ := identities_of_majority φ (fun i => liftAnswer i (pf.g i))
    P.signIndex (pf.c 0) (fun j => pf.c j.succ) hφ
    (fun i => degreeOf_liftAnswer_le i (pf.g i) (pf.degreeOf_g i))
    (pf.degreeOf_c 0) (fun j => pf.degreeOf_c j.succ)
    (by change 2 * (P.m' * 41) ≤ Fintype.card F; omega)
    S (fun z hz => (typedAccepts_ev_iff φ pf z).mp (hS z hz)) hmajority
  obtain ⟨i, hi⟩ := clause_satisfied_of_identities φ (fun i => liftAnswer i (pf.g i))
    P.signIndex (fun j => pf.c j.succ) (h₀.symm.trans h₁) y hy
  refine ⟨i, coded_eq_of_eval_eq_ofBool _ _ _ ?_⟩
  have he : P.block i (pt y : Fin P.m' → F) = pt (P.block i y) := rfl
  rw [eval_liftAnswer, he] at hi
  exact hi
end MIPRE.SAT.PcpAlgebra
