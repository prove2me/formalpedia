-- Prove2me | solution 1 for MIPRE.Halting.classV_efficient
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:22:40.342401+00:00
-- url     : https://prove2.me/submissions/09a8c0ca-7f5f-49fe-ae12-da82ee5fdce6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (solution of MIPRE.Halting.classV_efficient);
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
import Theorems.Thm_MIPRE_Halting_decProg_accepts
import Theorems.Thm_MIPRE_Halting_decProg_runs
import Theorems.Thm_MIPRE_Halting_sampProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Decider
open Cost
open Cost Cost.Prog
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data)
/-- Acceptance when the datum is the encoding of a program `dec`: the universal machine's run
is a run of `dec` (`UniversalMachine.time_le`, `halts_of`). -/
theorem wrap_accepts_prog (dec : Prog) (n : ℕ) (x y a b : BitStr) :
    (wrap U S (encode dec)).Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) := by
  rw [wrap_accepts]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun ⟨t, h⟩ => ?_, fun ⟨t, h⟩ => ?_⟩
  · exact U.halts_of dec _ _ _ h
  · obtain ⟨t', -, h'⟩ := U.time_le dec _ _ t h
    exact ⟨t', h'⟩
end MIPRE.Decider

namespace MIPRE.Verifier
open Cost
open Cost
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (decD : Data) (dec : Prog)
theorem ofSamplerDecider_accepts (n : ℕ) (x y a b : BitStr) :
    (ofSamplerDecider U S dec).decider.Accepts n x y a b ↔
      (x.length = S.dim n ∧ y.length = S.dim n ∧
        ∃ t, dec.Runs (encode (n, x, y, a, b)) (encode true) t) :=
  Decider.wrap_accepts_prog U S dec n x y a b
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem cutz_le (z : BitStr) : cutz G Λ₀ K R z ≤ cutB G Λ₀ K R z.length := by
  unfold cutz cutB
  set D := G.bound.natDegree
  set lam := lamz Λ₀ R z
  have h1 : esize lam ≤ 4 * Nat.size lam + 1 := esize_nat_le _
  have h2 : 2 ^ Nat.size lam ≤ 2 * lam + 1 := two_pow_size_le _
  have h3 : lam ≤ lamB Λ₀ R z.length := lamz_le Λ₀ R z z.length le_rfl
  calc 2 ^ (K + D * esize lam) ≤ 2 ^ (K + D * (4 * Nat.size lam + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left (Nat.mul_le_mul_left D h1) K)
    _ = 2 ^ (K + D) * (2 ^ Nat.size lam) ^ (4 * D) := by
        rw [show K + D * (4 * Nat.size lam + 1) = (K + D) + Nat.size lam * (4 * D) by ring,
          pow_add, pow_mul]
    _ ≤ 2 ^ (K + D) * (2 * lam + 1) ^ (4 * D) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ ≤ 2 ^ (K + D) * (2 * lamB Λ₀ R z.length + 1) ^ (4 * D) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem sampB_le (m : ℕ) : sampB G U Λ₀ R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_sampB G U Λ₀ R).le_poly_eval m; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem decB_le (m : ℕ) : decB G U UT Λ₀ K R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_decB G U UT Λ₀ K R).le_poly_eval m; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem cutB_le (m : ℕ) : cutB G Λ₀ K R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_cutB G Λ₀ K R).le_poly_eval m; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem cutz_le_B (z : BitStr) : cutz G Λ₀ K R z ≤ (classV G U UT Λ₀ K R).B z :=
  (cutz_le G Λ₀ K R z).trans (cutB_le G U UT Λ₀ K R _)
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem _root_.solution (z : BitStr) : (classV G U UT Λ₀ K R).Efficient z := by
  have hdim := dimz_le_B G U UT Λ₀ K R z
  refine ⟨fun r hr => ?_, fun x y a b => ?_, fun x y a b h => ?_⟩
  · obtain ⟨t, ht, hrun⟩ := sampProg_runs G U Λ₀ R z r (by rw [hr]; exact hdim)
    refine ⟨_, _, t, ht.trans (sampB_le G U UT Λ₀ K R _), ?_, ?_, hrun⟩
    · rw [qOf_length]; exact hdim
    · rw [qOf_length]; exact hdim
  · obtain ⟨r, t, ht, hrun⟩ := decProg_runs G U UT Λ₀ K R z x y a b
    exact ⟨r, t, ht.trans (decB_le G U UT Λ₀ K R _), hrun⟩
  · intro hacc
    obtain ⟨ha, hb, hV⟩ := (decProg_accepts G U UT Λ₀ K R z x y a b).1 hacc
    have hcut := cutz_le_B G U UT Λ₀ K R z
    rw [Vpaper, Vhalt, Verifier.ofSamplerDecider_accepts] at hV
    obtain ⟨hx, hy, -⟩ := hV
    have e : dimz G Λ₀ R z = (G.sampler (lamz Λ₀ R z)).dim (C G) := rfl
    rcases h with h | h | h | h <;> omega
end MIPRE.Halting
