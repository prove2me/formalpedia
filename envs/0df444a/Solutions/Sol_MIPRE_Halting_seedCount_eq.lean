-- Prove2me | solution 1 for MIPRE.Halting.seedCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:26:25.619767+00:00
-- url     : https://prove2.me/submissions/cf7aeea6-916b-444b-9256-4839f7637770

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (solution of MIPRE.Halting.seedCount_eq);
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
import Theorems.Thm_MIPRE_Cost_Data_length_filter_flatMap_bits
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Halting_classV_efficient
import Theorems.Thm_MIPRE_Halting_sampProg_runs
import Theorems.Thm_MIPRE_Verifier_length_filter_bitStrsOfLen

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

namespace MIPRE.Cost.Data
theorem bitStrsOfLen_succ (k : ℕ) :
    bitStrsOfLen (k + 1) = (bitStrsOfLen k).flatMap fun l => [false :: l, true :: l] := rfl
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
/-- **Counting by prefix**: the strings of length `d + e` whose first `d` bits satisfy `Q`
number the strings of length `d` satisfying `Q`, times `2 ^ e`. -/
theorem length_filter_take (Q : BitStr → Bool) (d e : ℕ) :
    ((bitStrsOfLen (d + e)).filter fun r => Q (r.take d)).length =
      ((bitStrsOfLen d).filter Q).length * 2 ^ e := by
  induction d generalizing Q with
  | zero =>
    simp only [Nat.zero_add, List.take_zero, bitStrsOfLen]
    cases hq : Q [] <;> simp [hq, length_bitStrsOfLen]
  | succ d ih =>
    rw [show d + 1 + e = d + e + 1 by omega, bitStrsOfLen_succ, bitStrsOfLen_succ,
      length_filter_flatMap_bits, length_filter_flatMap_bits]
    simp only [List.take_succ_cons]
    rw [ih (fun s => Q (false :: s)), ih (fun s => Q (true :: s)), Nat.add_mul]
end MIPRE.Cost.Data

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
theorem _root_.solution (z : BitStr) (x y : (Vz G U UT Λ₀ R z).Questions (C G)) :
    (classV G U UT Λ₀ K R).seedCount z (qEmb G U UT Λ₀ K R z x) (qEmb G U UT Λ₀ K R z y) =
      (Finset.univ.filter fun v : (Vz G U UT Λ₀ R z).Questions (C G) =>
        ((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval v = x ∧
          ((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval v = y).card *
        2 ^ ((classV G U UT Λ₀ K R).B z - dimz G Λ₀ R z) := by
  classical
  set d := dimz G Λ₀ R z with hd
  set B := (classV G U UT Λ₀ K R).B z with hB
  have hdB : d ≤ B := dimz_le_B G U UT Λ₀ K R z
  set L := ((Vz G U UT Λ₀ R z).sampler.cl (C G) .alice).eval
  set Rb := ((Vz G U UT Λ₀ R z).sampler.cl (C G) .bob).eval
  -- the seeds whose questions are `(x, y)` are those whose prefix maps to `(x, y)`
  have key : ∀ v w : (Vz G U UT Λ₀ R z).Questions (C G), toBits v = toBits w ↔ v = w :=
    fun v w => ⟨fun h => by rw [← ofBits_toBits v, h, ofBits_toBits], fun h => by rw [h]⟩
  have h1 : (classV G U UT Λ₀ K R).seedCount z (qEmb G U UT Λ₀ K R z x)
      (qEmb G U UT Λ₀ K R z y)
      = ((Data.bitStrsOfLen B).filter fun r =>
          decide (L (ofBits d (r.take d)) = x ∧ Rb (ofBits d (r.take d)) = y)).length := by
    unfold PolyVerifier.seedCount
    apply congrArg List.length
    refine List.filter_congr fun r hr => ?_
    have hr' : r.length = B := (Data.mem_bitStrsOfLen _ _).1 hr
    rw [classV_questions G U UT Λ₀ K R z r hr', decide_eq_decide, Prod.ext_iff]
    refine (and_congr Subtype.ext_iff Subtype.ext_iff).trans ?_
    show (toBits (L (ofBits d (r.take d))) = toBits x ∧
        toBits (Rb (ofBits d (r.take d))) = toBits y) ↔ _
    rw [key, key]
  rw [h1]
  have h2 := Data.length_filter_take (fun s => decide (L (ofBits d s) = x ∧ Rb (ofBits d s) = y))
    d (B - d)
  rw [Nat.add_sub_cancel' hdB] at h2
  rw [h2, show ((Data.bitStrsOfLen d).filter fun s =>
      decide (L (ofBits d s) = x ∧ Rb (ofBits d s) = y)).length =
      (Finset.univ.filter fun v => decide (L v = x ∧ Rb v = y) = true).card from
      length_filter_bitStrsOfLen (s := d) (fun v => decide (L v = x ∧ Rb v = y))]
  congr 1
  apply congrArg Finset.card
  ext v
  simp
end MIPRE.Halting
