-- Prove2me | solution 1 for MIPRE.Verifier.exists_isBounded_lam
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:01:13.198097+00:00
-- url     : https://prove2.me/submissions/067007e4-0c93-4fed-b58e-ab0c1731fb53

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Bounded.lean (solution of MIPRE.Verifier.exists_isBounded_lam);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
open Cost
/-- A program of polynomially bounded cost meets a single `n ^ λ` time bound at degree `λ`,
for every `n ≥ 2`. The degree and the coefficient are chosen together: `PolyBounded.exists_le_pow`
supplies a `λ` above which the coefficient fits under `n ^ λ`, and the degree of the cost is
absorbed by raising `λ` further. -/
theorem Prog.HasPolyCost.exists_bound {p : Prog} (h : p.HasPolyCost) :
    ∃ lam, ∀ n, 2 ≤ n → ∀ d : Data,
      HaltsWithin p (.cons (encode n) d) (n ^ lam * (d.size + 1) ^ lam) := by
  obtain ⟨C, k, hC, hrun⟩ := h
  obtain ⟨lam₀, hlam₀⟩ := hC.exists_le_pow
  refine ⟨max lam₀ k, fun n hn d => ?_⟩
  obtain ⟨r, t, ht, hrun⟩ := hrun n d
  refine ⟨r, t, ht.trans (Nat.mul_le_mul ?_ ?_), hrun⟩
  · exact (hlam₀ n hn).trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  · exact Nat.pow_le_pow_right (by omega) (le_max_right _ _)
end MIPRE.Cost

namespace MIPRE
open Cost
/-- The decider form of `Prog.HasPolyCost.exists_bound`. -/
theorem Decider.timeBoundAt_of_hasPolyCost {D : Decider} (h : D.prog.HasPolyCost) :
    ∃ lam, ∀ n, 2 ≤ n → D.TimeBoundAt n (n ^ lam) lam := by
  obtain ⟨lam, hlam⟩ := h.exists_bound
  exact ⟨lam, fun n hn d => hlam n hn d⟩
end MIPRE

namespace MIPRE
open Cost
/-- The sampler form of `Prog.HasPolyCost.exists_bound`. -/
theorem CL.Sampler.timeBoundAt_of_hasPolyCost {ℓ : ℕ} {S : CL.Sampler ℓ}
    (h : S.prog.HasPolyCost) : ∃ lam, ∀ n, 2 ≤ n → S.TimeBoundAt n (n ^ lam) lam := by
  obtain ⟨lam, hlam⟩ := h.exists_bound
  exact ⟨lam, fun n hn d => hlam n hn d⟩
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem _root_.solution (hdim : PolyBounded V.sampler.dim)
    (hS : V.sampler.prog.HasPolyCost) (hD : V.decider.prog.HasPolyCost) :
    ∃ lam, V.IsBounded lam := by
  obtain ⟨lamS, hlamS⟩ := CL.Sampler.timeBoundAt_of_hasPolyCost hS
  obtain ⟨lamD, hlamD⟩ := Decider.timeBoundAt_of_hasPolyCost hD
  obtain ⟨lamdim, hlamdim⟩ := hdim.exists_le_pow
  refine ⟨max (max lamS lamD) (max lamdim V.size), fun n hn => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hlamdim n hn).trans (Nat.pow_le_pow_right (by omega)
      ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (hlamS n hn).mono
      (Nat.pow_le_pow_right (by omega) ((le_max_left _ _).trans (le_max_left _ _)))
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hlamD n hn).mono
      (Nat.pow_le_pow_right (by omega) ((le_max_right _ _).trans (le_max_left _ _)))
      ((le_max_right _ _).trans (le_max_left _ _))
  · exact (le_max_right _ _).trans (le_max_right _ _)
end MIPRE.Verifier
