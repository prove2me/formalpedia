-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryProgram.readingCheck_vectors
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:57:14.034785+00:00
-- url     : https://prove2.me/submissions/2363365a-dda1-4593-8955-1f3f5f180a75

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryReadProgram.lean (solution of MIPRE.Introspection.AuxiliaryProgram.readingCheck_vectors);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_AnswerParser_field_append_injective
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_equal_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairBits_injective {y a z b : BitStr} (h : pairBits y a = pairBits z b) :
    y = z ∧ a = b := by
  obtain ⟨hy, ha⟩ := field_append_injective y z (field a) (field b) h
  exact ⟨hy, (field_append_injective a b [] [] (by simpa using ha)).1⟩
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem tripleBits_injective {y yp a z zp b : BitStr}
    (h : tripleBits y yp a = tripleBits z zp b) : y = z ∧ yp = zp ∧ a = b := by
  obtain ⟨hy, hr⟩ := field_append_injective y z (pairBits yp a) (pairBits zp b) h
  exact ⟨hy, pairBits_injective hr⟩
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairCheck_apply (Q R : ℕ) (bs : BitStr) :
    pairCheck Q R bs = decide (pairValid Q R bs) := by
  simp only [pairCheck, pairValid, PolyTimeFun.ite_apply, ap₂_apply, comp_apply,
    encoded_apply, treeEq_apply, pairBitsProg_apply, pairPartsProg_apply, fst_apply,
    snd_apply, lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
    encode_injective.eq_iff, decide_eq_true_eq]
  rw [decide_and_if, decide_and_if]
  rfl
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem tripleCheck_apply (Q R : ℕ) (exactLast : Bool) (bs : BitStr) :
    tripleCheck Q R exactLast bs = decide (tripleValid Q R exactLast bs) := by
  cases exactLast <;>
    simp only [tripleCheck, tripleValid, Bool.false_eq_true,
      if_false, if_true, PolyTimeFun.ite_apply, ap₂_apply, comp_apply,
      encoded_apply, treeEq_apply, tripleBitsProg_apply, triplePartsProg_apply, fst_apply,
      snd_apply, lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
      encode_injective.eq_iff, decide_eq_true_eq] <;>
    rw [decide_and_if, decide_and_if, decide_and_if]
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairCheck_iff (Q R : ℕ) (bs : BitStr) : pairCheck Q R bs = true ↔
    ∃ y a, y.length = Q ∧ a.length ≤ R ∧ bs = pairBits y a := by
  rw [pairCheck_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hy, ha⟩
    exact ⟨_, _, hy, ha, h⟩
  · rintro ⟨y, a, hy, ha, rfl⟩
    simp [pairValid, pairParts_pairBits Q y a hy, hy, ha]
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem tripleCheck_iff (Q R : ℕ) (exactLast : Bool) (bs : BitStr) :
    tripleCheck Q R exactLast bs = true ↔
      ∃ y yp a, y.length = Q ∧ yp.length = Q ∧
        (if exactLast then a.length = R else a.length ≤ R) ∧ bs = tripleBits y yp a := by
  rw [tripleCheck_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hy, hyp, ha⟩
    exact ⟨_, _, _, hy, hyp, ha, h⟩
  · rintro ⟨y, yp, a, hy, hyp, ha, rfl⟩
    simp [tripleValid, tripleParts_tripleBits Q y yp a hy hyp, hy, hyp, ha]
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
/-- In particular, an encoded pair with a wrong register length or long `a` is rejected. -/
theorem pairCheck_pairBits (Q R : ℕ) (y a : BitStr) :
    pairCheck Q R (pairBits y a) = true ↔ y.length = Q ∧ a.length ≤ R := by
  rw [pairCheck_iff]
  constructor
  · rintro ⟨z, b, hz, hb, he⟩
    obtain ⟨rfl, rfl⟩ := pairBits_injective he
    exact ⟨hz, hb⟩
  · rintro ⟨hy, ha⟩
    exact ⟨y, a, hy, ha, rfl⟩
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem tripleCheck_tripleBits (Q R : ℕ) (exactLast : Bool) (y yp a : BitStr) :
    tripleCheck Q R exactLast (tripleBits y yp a) = true ↔
      y.length = Q ∧ yp.length = Q ∧
        (if exactLast then a.length = R else a.length ≤ R) := by
  rw [tripleCheck_iff]
  constructor
  · rintro ⟨z, zp, b, hz, hzp, hb, he⟩
    obtain ⟨rfl, rfl, rfl⟩ := tripleBits_injective he
    exact ⟨hz, hzp, hb⟩
  · rintro ⟨hy, hyp, ha⟩
    exact ⟨y, yp, a, hy, hyp, ha, rfl⟩
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
/-- The repaired strict `8Q` outer cutoff contains every honest pair tuple. -/
theorem pairBits_lt_outer (Q R : ℕ) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (y a : BitStr) (hy : y.length = Q) (ha : a.length ≤ R) :
    (pairBits y a).length < 8 * Q := by rw [pairBits_length, hy]; omega
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
/-- The repaired strict `8Q` outer cutoff contains every honest Read tuple. -/
theorem readBits_lt_outer (Q R : ℕ) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (y yp a : BitStr) (hy : y.length = Q) (hyp : yp.length = Q) (ha : a.length ≤ R) :
    (tripleBits y yp a).length < 8 * Q := by rw [tripleBits_length, hy, hyp]; omega
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.DynamicParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairCheck_apply (bs : BitStr) (Q R : ℕ) :
    pairCheck (bs, Q, R) = decide (AnswerParser.pairValid Q R bs) := by
  simp only [pairCheck, AnswerParser.pairValid, PolyTimeFun.ite_apply, ap₂_apply,
    comp_apply, pair_apply, fst_apply, snd_apply, encoded_apply, treeEq_apply,
    AnswerParser.pairBitsProg_apply, pairParts_apply, lengthNat_apply,
    SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply, encode_injective.eq_iff,
    decide_eq_true_eq]
  rw [decide_and_if, decide_and_if]
  rfl
end
end MIPRE.Introspection.DynamicParser

namespace MIPRE.Introspection.DynamicParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem tripleCheck_apply (bs : BitStr) (Q R : ℕ) (exactLast : Bool) :
    tripleCheck exactLast (bs, Q, R) = decide (AnswerParser.tripleValid Q R exactLast bs) := by
  cases exactLast <;>
    simp only [tripleCheck, AnswerParser.tripleValid, Bool.false_eq_true, if_false, if_true,
      PolyTimeFun.ite_apply, ap₂_apply, comp_apply, pair_apply, fst_apply, snd_apply,
      encoded_apply, treeEq_apply, AnswerParser.tripleBitsProg_apply, tripleParts_apply,
      lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
      encode_injective.eq_iff, decide_eq_true_eq] <;>
    rw [decide_and_if, decide_and_if, decide_and_if]
end
end MIPRE.Introspection.DynamicParser

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem outerCheck_iff (x : GuardInput) : outerCheck x = true ↔
    (inputLeft x).length < 8 * inputQ x ∧ (inputRight x).length < 8 * inputQ x := by
  simp only [outerCheck, andCheck_iff, ap₂_apply, comp_apply, leNat_apply,
    decide_eq_true_eq, inc_apply, lengthNat_apply, SourceCompiler.eight_apply,
    Nat.add_one_le_iff]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem readingCheck_iff (x : GuardInput) : readingCheck x = true ↔
    (inputLeft x).length < 8 * inputQ x ∧ (inputRight x).length < 8 * inputQ x ∧
    AnswerParser.pairValid (inputQ x) (inputR x) (inputLeft x) ∧
    AnswerParser.tripleValid (inputQ x) (inputR x) false (inputRight x) ∧
    (leftParts x).1 = (rightTriple x).1 ∧ (leftParts x).2 = (rightTriple x).2.2 := by
  simp only [readingCheck, andCheck_iff, outerCheck_iff, pairLeft, readRight,
    comp_apply, pair_apply, DynamicParser.pairCheck_apply, DynamicParser.tripleCheck_apply,
    decide_eq_true_eq, equal_iff, fst_apply, snd_apply, and_assoc]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem toBits_injective {Q : ℕ} : Function.Injective (@CL.toBits Q) := by
  intro x y h
  simpa only [CL.ofBits_toBits] using congrArg (CL.ofBits Q) h
end
end MIPRE.Introspection.AuxiliaryProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem _root_.solution {Q R : ℕ} (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (n s : ℕ) (y z zp : Fin Q → CL.𝔽₂) (a b : BitStr) :
    readingCheck (n,Q,R,s,AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) b) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧ CLChecks.reading (y,a) (z,zp,b) := by
  have hpair := AnswerParser.pairCheck_pairBits Q R (CL.toBits y) a
  have hread := AnswerParser.tripleCheck_tripleBits Q R false (CL.toBits z) (CL.toBits zp) b
  rw [AnswerParser.pairCheck_apply] at hpair
  rw [AnswerParser.tripleCheck_apply] at hread
  simp only [decide_eq_true_eq, CL.length_toBits, true_and,
    Bool.false_eq_true, if_false] at hpair hread
  rw [readingCheck_iff]
  simp only [SourceCompiler.inputQ, SourceCompiler.inputR, SourceCompiler.inputLeft,
    SourceCompiler.inputRight, SourceCompiler.leftParts, rightTriple,
    comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.pairParts_apply,
    DynamicParser.tripleParts_apply, AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),
    AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
    hpair, hread, toBits_injective.eq_iff, CLChecks.reading]
  constructor
  · rintro ⟨_,_,ha,hb,he⟩
    exact ⟨ha,hb,he⟩
  · rintro ⟨ha,hb,he⟩
    exact ⟨AnswerParser.pairBits_lt_outer Q R hQ hR _ _ (CL.length_toBits _) ha,
      AnswerParser.readBits_lt_outer Q R hQ hR _ _ _ (CL.length_toBits _) (CL.length_toBits _) hb,
      ha,hb,he⟩
end MIPRE.Introspection.AuxiliaryProgram
