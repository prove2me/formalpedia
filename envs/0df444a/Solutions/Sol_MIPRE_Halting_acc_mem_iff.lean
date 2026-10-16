-- Prove2me | solution 1 for MIPRE.Halting.acc_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:38:19.102213+00:00
-- url     : https://prove2.me/submissions/cb66c2cd-169a-4269-8f7a-54fd5fceaed8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Instantiation.lean (solution of MIPRE.Halting.acc_mem_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
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
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
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
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Machine_runs_of_runForD
import Theorems.Thm_MIPRE_Verifier_answerEquiv_symm_val
import Theorems.Thm_MIPRE_Verifier_mem_accListW_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Machine
/-- **The decision procedure.** For a program that halts within the budget, whether it returns
a given value is decidable. -/
theorem runForD_eq_some_iff {p : Prog} {x r : Data} {k : ℕ}
    (hb : HaltsWithin p x k) : runForD (encode p) x k = some r ↔ ∃ t, p.Runs x r t := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb
  refine ⟨runs_of_runForD, fun ⟨t, h⟩ => ?_⟩
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact runForD_eq_some h₀ ht₀
end MIPRE.Cost.Machine

namespace MIPRE.Decider
open Cost
open HaltingGameValue (GameData)
variable (D : Decider)
/-- **Acceptance under a time bound is one budgeted run.** -/
theorem accepts_iff_runForD {n T k : ℕ} (hb : D.TimeBoundAt n T k) (x y a b : BitStr) :
    D.Accepts n x y a b ↔
      Machine.runForD (encode D.prog) (encode (n, x, y, a, b))
        (acceptBudget T k x y a b) = some (encode true) :=
  (Machine.runForD_eq_some_iff (hb (encode (x, y, a, b)))).symm
end MIPRE.Decider

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **Acceptance by an `n`-bounded verifier is one budgeted run**, at the budget its own
`λ`-boundedness supplies. This is what fills in the acceptance table of the tabulation. -/
theorem accepts_iff_runForD {n : ℕ} (hb : V.IsBounded n) (hn : 2 ≤ n) (x y a b : BitStr) :
    V.decider.Accepts n x y a b ↔
      Machine.runForD (encode V.decider.prog) (encode (n, x, y, a, b))
        (Decider.acceptBudget (n ^ n) n x y a b) = some (encode true) :=
  V.decider.accepts_iff_runForD (hb.1 n hn).2.2 x y a b
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
/-- **Reading a packed index back.** -/
theorem bitsToIdx_tagEquiv_symm (s : ℕ) (i : Fin (2 ^ (s + 1))) :
    bitsToIdx (((tagEquiv s).symm i).1 :: CL.toBits ((tagEquiv s).symm i).2) = (i : ℕ) :=
  congrArg Fin.val ((tagEquiv s).apply_symm_apply i)
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem decProgData_eq (x : BitStr) : decProgData G U x = encode ((Vof G U x).decider.prog) := by
  rw [decProgData, sampData_eq, Prog.ProgD.dWrapCore_eq]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- The tabulated acceptance test **is** the verifier's acceptance, on an `n`-bounded
verifier. -/
theorem accOf_iff (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n) (x' y' a b : BitStr) :
    accOf (decProgData G U x) n x' y' a b = true ↔
      (Vof G U x).decider.Accepts n x' y' a b := by
  rw [accOf, decide_eq_true_iff, decProgData_eq,
    ← (Vof G U x).accepts_iff_runForD hb hb.two_le x' y' a b]
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem eXof_apply (x : BitStr) (n : ℕ)
    (i : Fin ((tab G U x n).nX + 1)) :
    Verifier.bitsToIdx ((eXof G U x n i).1 :: CL.toBits (eXof G U x n i).2) = (i : ℕ) := by
  rw [eXof, Equiv.trans_apply, Verifier.bitsToIdx_tagEquiv_symm]
  simp
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem eAof_apply (x : BitStr) (n : ℕ) (k : Fin ((tab G U x n).nA + 1)) :
    (Data.bitStrsLE (ansBound G x n)).idxOf (eAof G U x n k).1 = (k : ℕ) := by
  rw [← Verifier.answerEquiv_symm_val, eAof]
  simp
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded n)
    (i j : Fin ((tab G U x n).nX + 1)) (k l : Fin ((tab G U x n).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (tab G U x n).acc
      ↔ ((eXof G U x n i).1 = false ∧ (eXof G U x n j).1 = true ∧
          (Vof G U x).decider.Accepts n (CL.toBits (eXof G U x n i).2)
            (CL.toBits (eXof G U x n j).2) (eAof G U x n k).1 (eAof G U x n l).1) := by
  have hdim : dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n := dimOf_eq G U x n
  have hqmem : ∀ (m : Fin ((tab G U x n).nX + 1)),
      CL.toBits (eXof G U x n m).2 ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n) := by
    intro m
    rw [Data.mem_bitStrsOfLen, CL.length_toBits, hdim]
  have hamem : ∀ (m : Fin ((tab G U x n).nA + 1)),
      (eAof G U x n m).1 ∈ Data.bitStrsLE (ansBound G x n) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (eAof G U x n m).2
  rw [show (tab G U x n).acc = Verifier.accListW (dimOf (sampData G x) (ansBound G x n) G.deg n) (ansBound G x n)
      (fun u => Verifier.bitsToIdx (false :: u)) (fun v => Verifier.bitsToIdx (true :: v))
      (accOf (decProgData G U x) n) from rfl, Verifier.mem_accListW_iff]
  constructor
  · rintro ⟨u, hu, v, hv, a, ha, b, hb', hacc, hi, hj, hk, hl⟩
    have hu' : (eXof G U x n i).1 = false ∧ CL.toBits (eXof G U x n i).2 = u :=
      List.cons_eq_cons.mp (Verifier.bitsToIdx_injOn
        (s := (Vof G U x).sampler.dim n + 1) (by simp)
        (by rw [List.length_cons, (Data.mem_bitStrsOfLen _ _).1 hu, hdim])
        (by rw [eXof_apply G U x n i, hi]))
    have hv' : (eXof G U x n j).1 = true ∧ CL.toBits (eXof G U x n j).2 = v :=
      List.cons_eq_cons.mp (Verifier.bitsToIdx_injOn
        (s := (Vof G U x).sampler.dim n + 1) (by simp)
        (by rw [List.length_cons, (Data.mem_bitStrsOfLen _ _).1 hv, hdim])
        (by rw [eXof_apply G U x n j, hj]))
    have ha' : a = (eAof G U x n k).1 := (List.idxOf_inj ha).1 (by rw [← hk, eAof_apply])
    have hb'' : b = (eAof G U x n l).1 := (List.idxOf_inj hb').1 (by rw [← hl, eAof_apply])
    refine ⟨hu'.1, hv'.1, ?_⟩
    rw [hu'.2, hv'.2, ← ha', ← hb'']
    exact (accOf_iff G U x n hb _ _ _ _).1 hacc
  · rintro ⟨ht1, ht2, h⟩
    refine ⟨_, hqmem i, _, hqmem j, _, hamem k, _, hamem l,
      (accOf_iff G U x n hb _ _ _ _).2 h, ?_, ?_,
      (eAof_apply G U x n k).symm, (eAof_apply G U x n l).symm⟩
    · rw [← ht1, eXof_apply G U x n i]
    · rw [← ht2, eXof_apply G U x n j]
end MIPRE.Halting
