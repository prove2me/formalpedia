-- Prove2me | solution 1 for MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:34.795174+00:00
-- url     : https://prove2.me/submissions/510c7f1f-8b4e-4a65-b78c-157278670ab1

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/PcpBlocks.lean (solution of MIPRE.SAT.PcpAlgebra.exists_proof_of_satisfying_assignment);
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
import Theorems.Thm_MIPRE_LowDegree_degreeOf_ind_le
import Theorems.Thm_MIPRE_LowDegree_exists_zero_basis
import Theorems.Thm_MIPRE_SAT_PcpAlgebra_literal_product_degree_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {F : Type*} [CommRing F] {m : ℕ}
theorem degreeOf_ldEnc_le [Nontrivial F] (a : (Fin m → Bool) → F) (i : Fin m) :
    (ldEnc a).degreeOf i ≤ 1 := by
  rw [ldEnc]
  refine (MvPolynomial.degreeOf_sum_le i univ (fun y => C (a y) * ind y)).trans ?_
  refine Finset.sup_le fun y _ => ?_
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans (by simpa using degreeOf_ind_le (F := F) y i)
end
end MIPRE.LowDegree

namespace MIPRE.SAT.PcpAlgebra
noncomputable section
open Finset MvPolynomial LowDegree
variable {P : PcpParams} {F : Type*} [Field F]
/-- The honest constraint has individual degree at most seven. -/
theorem honest_constraint_degree_le (φ : MvPolynomial (Fin P.m') F)
    (g : Fin 5 → MvPolynomial (Fin P.m) F)
    (hφ : ∀ j, φ.degreeOf j ≤ 6) (hg : ∀ i j, (g i).degreeOf j ≤ 1)
    (j : Fin P.m') :
    (constraint φ (fun i => liftAnswer i (g i)) P.signIndex).degreeOf j ≤ 7 :=
  (degreeOf_mul_le j _ _).trans (Nat.add_le_add (hφ j) (literal_product_degree_le g hg j))
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
theorem _root_.solution
    (φ : MvPolynomial (Fin P.m') F) (hφdeg : ∀ j, φ.degreeOf j ≤ 6)
    (hφbool : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 0 ∨ eval (pt y) φ = 1)
    (a : Fin 5 → (Fin P.m → Bool) → Bool)
    (hsat : ∀ y : Fin P.m' → Bool, eval (pt y) φ = 1 →
      ∃ i : Fin 5, a i (P.block i y) = y (P.signIndex i)) :
    ∃ pf : PcpProof P F,
      (∀ i, pf.g i = ldEnc (fun x => ofBool (a i x))) ∧
      ∀ z, TypedAccepts φ z (pf.ev z) := by
  let g : Fin 5 → MvPolynomial (Fin P.m) F := fun i => ldEnc (fun x => ofBool (a i x))
  have hg : ∀ i j, (g i).degreeOf j ≤ 1 := fun i => degreeOf_ldEnc_le _
  let c₀ := constraint φ (fun i => liftAnswer i (g i)) P.signIndex
  have hc₀ : ∀ j, c₀.degreeOf j ≤ 7 := honest_constraint_degree_le φ g hφdeg hg
  have hz : ∀ y : Fin P.m' → Bool, eval (pt y) c₀ = 0 := by
    intro y
    simp only [c₀, constraint, map_mul, map_prod, map_sub, eval_X, eval_liftAnswer]
    rcases hφbool y with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul]
      obtain ⟨i, hi⟩ := hsat y h
      apply Finset.prod_eq_zero (mem_univ i)
      have he : P.block i (pt y : Fin P.m' → F) = pt (P.block i y) := rfl
      simp [he, g, hi, pt]
  obtain ⟨c, hc, hd⟩ := exists_zero_basis c₀ hc₀ hz
  let pf : PcpProof P F :=
    { g := g
      c := Fin.cases c₀ c
      degreeOf_g := fun i j => (hg i j).trans (by decide)
      degreeOf_c := by
        intro i
        refine Fin.cases hc₀ (fun j => hd j) i }
  refine ⟨pf, fun _ => rfl, fun z => (typedAccepts_ev_iff φ pf z).mpr ?_⟩
  refine ⟨rfl, ?_⟩
  exact congrArg (eval z) hc
end MIPRE.SAT.PcpAlgebra
