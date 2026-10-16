-- Prove2me | solution 1 for MIPRE.Halting.classV_game_support
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:42:58.584985+00:00
-- url     : https://prove2.me/submissions/8bbf2c4c-3d3f-4912-8ead-68ed80cd9094

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (solution of MIPRE.Halting.classV_game_support);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound
import Definitions.Def_MIPRE_Foundations_Halting_Absorb
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Size
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Cost
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Stages
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Build
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Main
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassVerifier
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassMain
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Halting_classV_efficient
import Theorems.Thm_MIPRE_Halting_sampProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
theorem encode_injective {α : Type*} [SizedEncoding α] : Function.Injective (encode : α → Data) := by
  intro a b h
  have := SizedEncoding.decode_encode a
  rw [h, SizedEncoding.decode_encode] at this
  exact (Option.some.inj this).symm
end MIPRE.Cost

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
variable (V : PolyVerifier)
theorem sample?_eq_some_iff (z r : BitStr) (p : BitStr × BitStr) :
    V.sample? z r = some p ↔ ∃ t, V.sampler.Runs (encode (z, r)) (encode p) t := by
  unfold sample?
  split_ifs with h
  · obtain ⟨t, ht⟩ := h.choose_spec
    constructor
    · rintro ⟨rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t', ht'⟩
      obtain ⟨he, -⟩ := ht.deterministic ht'
      have := SizedEncoding.decode_encode (α := BitStr × BitStr) h.choose
      rw [he, SizedEncoding.decode_encode] at this
      rw [Option.some.injEq] at this
      rw [this]
  · simp only [false_iff, not_exists]
    exact fun t ht => h ⟨p, t, ht⟩
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
variable (V : PolyVerifier)
/-- On an efficient verifier the sampler's output on a seed of the right length is the
question pair, with no fallback. -/
theorem questions_eq_of_efficient {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r.length = V.B z) :
    ∃ (x y : BitStr) (t : ℕ), t ≤ V.bound.eval (z.length + r.length) ∧
      V.sampler.Runs (encode (z, r)) (encode (x, y)) t ∧
      (V.questions z r).1.1 = x ∧ (V.questions z r).2.1 = y := by
  obtain ⟨x, y, t, ht, hx, hy, hrun⟩ := h.sampler_runs r hr
  refine ⟨x, y, t, ht, hrun, ?_⟩
  have hs : V.sample? z r = some (x, y) := (V.sample?_eq_some_iff z r (x, y)).2 ⟨t, hrun⟩
  simp only [questions, hs, hx, hy, and_self, dite_true]
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
variable (V : PolyVerifier)
theorem game_μ (z : BitStr) (x y : Answers (V.B z)) :
    (V.game z).μ x y = (V.seedCount z x y : ℝ) / 2 ^ V.B z := rfl
end MIPRE.PolyVerifier

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
/-- The question pair of a seed of the right length. -/
theorem classV_questions (z r : BitStr) (hr : r.length = (classV G U UT Λ₀ K R).B z) :
    (classV G U UT Λ₀ K R).questions z r =
      (⟨qOf G Λ₀ R .alice z r, by rw [qOf_length]; exact dimz_le_B G U UT Λ₀ K R z⟩,
        ⟨qOf G Λ₀ R .bob z r, by rw [qOf_length]; exact dimz_le_B G U UT Λ₀ K R z⟩) := by
  obtain ⟨x, y, t, -, hrun, hx, hy⟩ :=
    (classV G U UT Λ₀ K R).questions_eq_of_efficient (classV_efficient G U UT Λ₀ K R z) hr
  obtain ⟨t', -, hrun'⟩ := sampProg_runs G U Λ₀ R z r
    (by rw [hr]; exact dimz_le_B G U UT Λ₀ K R z)
  obtain ⟨he, -⟩ := Eval.deterministic hrun hrun'
  have he' := encode_injective he
  simp only [Prod.mk.injEq] at he'
  exact Prod.ext (Subtype.ext (hx.trans he'.1)) (Subtype.ext (hy.trans he'.2))
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem _root_.solution (z : BitStr) (x' y' : Answers ((classV G U UT Λ₀ K R).B z))
    (h : ((classV G U UT Λ₀ K R).game z).μ x' y' ≠ 0) :
    (∃ x, qEmb G U UT Λ₀ K R z x = x') ∧ ∃ y, qEmb G U UT Λ₀ K R z y = y' := by
  classical
  rw [PolyVerifier.game_μ] at h
  have hc : (classV G U UT Λ₀ K R).seedCount z x' y' ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  unfold PolyVerifier.seedCount at hc
  have hne : ((Data.bitStrsOfLen ((classV G U UT Λ₀ K R).B z)).filter fun r =>
      decide ((classV G U UT Λ₀ K R).questions z r = (x', y'))) ≠ [] :=
    fun h0 => hc (by rw [h0]; rfl)
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hr, hq⟩ := List.mem_filter.1 hr
  have hq := of_decide_eq_true hq
  have hr' : r.length = (classV G U UT Λ₀ K R).B z := (Data.mem_bitStrsOfLen _ _).1 hr
  rw [classV_questions G U UT Λ₀ K R z r hr'] at hq
  obtain ⟨hq1, hq2⟩ := Prod.ext_iff.1 hq
  exact ⟨⟨((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval
      (ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))), hq1⟩,
    ⟨((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval
      (ofBits (dimz G Λ₀ R z) (r.take (dimz G Λ₀ R z))), hq2⟩⟩
end MIPRE.Halting
