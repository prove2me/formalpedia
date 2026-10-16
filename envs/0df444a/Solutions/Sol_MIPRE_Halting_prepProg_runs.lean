-- Prove2me | solution 1 for MIPRE.Halting.prepProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:20:47.244363+00:00
-- url     : https://prove2.me/submissions/4d655a21-56ee-4074-baa1-778422f9fdc3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Compressor.lean (solution of MIPRE.Halting.prepProg_runs);
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
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Theorems.Thm_MIPRE_Cost_Data_encode_natOf
import Theorems.Thm_MIPRE_Cost_Data_size_sum_stackStep_le
import Theorems.Thm_MIPRE_Cost_Prog_normBinProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_parseProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_readProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Machine
open Prog
theorem size_left_le (d : Data) : d.left.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Data
/-- Normalization does not grow a datum: it is either the datum or `nil`. -/
theorem size_normBin_le (d : Data) : (normBin d).size ≤ d.size := by
  unfold normBin
  split
  · exact le_rfl
  · have := d.size_pos
    simp only [size_nil]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
/-- So the whole run adds at most the length of the string. -/
theorem size_sum_stackRun_le (x : BitStr) (s : List Data) :
    ((stackRun x s).map size).sum ≤ (s.map size).sum + x.length := by
  induction x generalizing s with
  | nil => simp
  | cons bit x ih =>
    rw [stackRun_cons]
    have h1 := ih (stackStep s bit)
    have h2 := size_sum_stackStep_le s bit
    simp only [List.length_cons]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
/-- **What a string of length `L` can parse to**: a datum of size at most `L`, or `nil` when
the run leaves the stack empty. -/
theorem size_parse_le (x : BitStr) : (parse x).size ≤ max 1 x.length := by
  have h := size_sum_stackRun_le x []
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at h
  unfold parse
  rcases hs : stackRun x [] with _ | ⟨d, t⟩
  · simp
  · rw [hs] at h
    simp only [List.map_cons, List.sum_cons] at h
    simp only [List.headD_cons]
    exact le_max_of_le_right (by omega)
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
open Data
theorem normBinProg_wellScoped : normBinProg.WellScoped 1 := by
  simp [normBinProg, WellScoped, canonBody]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incProg_wellScoped : incProg.WellScoped 1 := by
  simp [incProg, WellScoped, incBody, revOntoProg, revOntoBody]
end MIPRE.Cost.Prog

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem decProgData_eq (x : BitStr) : decProgData G U x = encode ((Vof G U x).decider.prog) := by
  rw [decProgData, sampData_eq, Prog.ProgD.dWrapCore_eq]
  rfl
end MIPRE.Halting

namespace MIPRE.Cost.Prog
open Data
theorem parseProg_wellScoped : parseProg.WellScoped 1 := by simp [parseProg, WellScoped, parseBody]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
theorem readBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (readBody univ).WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, trivial, ⟨by simp [WellScoped], by simp [WellScoped]⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) hU, ?_⟩
  refine ⟨by decide, ⟨callVar_wellScoped (by decide) incProg_wellScoped, by simp [WellScoped]⟩, ?_⟩
  refine ⟨by decide, ⟨callVar_wellScoped (by decide) incProg_wellScoped, by simp [WellScoped]⟩,
    by simp [WellScoped]⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
theorem readProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (readProg univ).WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial, trivial⟩,
    ⟨⟨by decide, (readBody_wellScoped hU).mono (by omega) _⟩, revProg_wellScoped.mono (by omega) _⟩⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog.ProgD
open Cost
open Data
theorem dFreeze_eq (k : ℕ) (p : Prog) :
    dFreeze (encode k) (encode p) = encode (Prog.freezeProg k p) := rfl
end MIPRE.Cost.Prog.ProgD

namespace MIPRE.Cost.Prog.ProgD
open Cost
open Data
theorem size_dFreeze (kD p : Data) : (dFreeze kD p).size = p.size + kD.size + 53 := by
  simp only [dFreeze, size_dL, size_dE, size_dC, size_dK, size_dV, size_dNil]
  omega
end MIPRE.Cost.Prog.ProgD

namespace MIPRE.Cost.Prog
open Cost
open Data
open ProgD
theorem freezeBuildProg_wellScoped : freezeBuildProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, pL_wellScoped (pE_wellScoped trivial
    (pC_wellScoped (pK_wellScoped (by simp [WellScoped])) trivial)) (by simp [WellScoped])⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
open ProgD
theorem freezeBuildProg_runs (kD p : Data) :
    ∃ t ≤ p.size + kD.size + 56, freezeBuildProg.Runs (.cons kD p) (dFreeze kD p) t := by
  have run := Eval.elim_cons (env := [Data.cons kD p]) (i := 0) (n := .nil) (a := kD) (b := p)
    (by simp)
    (pL_eval (pE_eval 0 (Eval.const _ dNil)
      (pC_eval (pK_eval (Eval.var_of_get (i := 0) (v := kD) (by simp))) (Eval.const _ (dV 1))))
      (Eval.var_of_get (i := 1) (v := p) (by simp)))
  refine ⟨_, ?_, run⟩
  simp only [size_dV, size_dNil]
  omega
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
open ProgD
/-- The left projection on any datum (`nil` on `nil`). -/
theorem fstProg_runs' (d : Data) : ∃ t ≤ d.left.size + 2, fstProg.Runs d d.left t := by
  cases d with
  | nil => exact ⟨2, by simp [Data.left], Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
  | cons a b => exact ⟨_, le_rfl, fstProg_runs a b⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
open ProgD
/-- The right projection on any datum (`nil` on `nil`). -/
theorem sndProg_runs' (d : Data) : ∃ t ≤ d.right.size + 2, sndProg.Runs d d.right t := by
  cases d with
  | nil => exact ⟨2, by simp [Data.right], Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
  | cons a b => exact ⟨_, le_rfl, sndProg_runs a b⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Cost
open Data
open ProgD
theorem call2_eval {env : Env} {i j : ℕ} {q : Prog} (hq : q.WellScoped 1) {a b r : Data}
    {t : ℕ} (ha : env.get i = a) (hb : env.get j = b) (h : Eval [.cons a b] q r t) :
    Eval env (call2 i j q) r (a.size + b.size + t + 4) :=
  (Eval.let_ (Eval.cons (Eval.var_of_get ha) (Eval.var_of_get hb))
    (Eval.append_of_wellScoped h hq env)).cast_cost (by omega)
end MIPRE.Cost.Prog

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem encode_frozen_sampler (x : BitStr) (n : ℕ) :
    (encode (frozen G U x n).sampler.prog : Data) = dFreeze (kD n) (sampD G x) := by
  show encode (Prog.freezeProg (2 * n + 1) (G.sampler (descLam x)).prog) = _
  rw [← dFreeze_eq, Cost.encode_two_mul_add_one, ← G.samplerProg_eq]
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem encode_frozen_decider (x : BitStr) (n : ℕ) :
    (encode (frozen G U x n).decider.prog : Data) = dFreeze (kD n) (wD G U x) := by
  show encode (Prog.freezeProg (2 * n + 1) (Vof G U x).decider.prog) = _
  rw [← dFreeze_eq, Cost.encode_two_mul_add_one, ← decProgData_eq]
  rfl
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ) :
    ∃ t ≤ prepBound G U (esize c) n x.length (esize lam),
      (prepProg G U).Runs (encode (c, n, lam)) (compressedD G U x n lam) t := by
  -- the runs of the stages
  obtain ⟨t₁, ht₁, h₁⟩ := readProg_runs U hsd
  obtain ⟨t₂, ht₂, h₂⟩ := parseProg_runs x
  obtain ⟨t₃, ht₃, h₃⟩ := sndProg_runs' (Data.parse x)
  obtain ⟨t₄, ht₄, h₄⟩ := fstProg_runs' (Data.parse x)
  obtain ⟨t₅, ht₅, h₅⟩ := normBinProg_runs (Data.parse x).left
  obtain ⟨t₆, ht₆, h₆⟩ := G.samplerProg.computes (descLam x)
  obtain ⟨t₇, ht₇, h₇⟩ := wrapBuildProg_runs (encode U.univ) (sampD G x) (Data.parse x).right
  obtain ⟨t₈, ht₈, h₈⟩ := freezeBuildProg_runs (kD n) (sampD G x)
  obtain ⟨t₉, ht₉, h₉⟩ := freezeBuildProg_runs (kD n) (wD G U x)
  obtain ⟨t₁₀, ht₁₀, h₁₀⟩ := G.compress.computes
    (((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog), lam)
  -- the inputs of the sampler program and of `Compress`, as the stages before them produce them
  have h₆' : G.samplerProg.code.Runs (Data.normBin (Data.parse x).left) (sampD G x) t₆ := by
    rw [← Data.encode_natOf]; exact h₆
  have h₁₀' : G.compress.code.Runs
      (.cons (.cons (dFreeze (kD n) (sampD G x)) (dFreeze (kD n) (wD G U x))) (encode lam))
      (compressedD G U x n lam) t₁₀ := by
    rw [← encode_frozen_sampler, ← encode_frozen_decider]; exact h₁₀
  -- the run
  have run : Eval [encode (c, n, lam)] (prepProg G U) (compressedD G U x n lam) _ :=
    Eval.elim_cons (env := [encode (c, n, lam)]) (i := 0) (a := encode c)
      (b := .cons (encode n) (encode lam)) (by simp; rfl)
      (Eval.elim_cons (i := 1) (a := encode n) (b := encode lam) (by simp)
        (Eval.let_ (callVar_eval (readProg_wellScoped U.closed) (i := 2) (v := encode c) (by simp) h₁)
          (Eval.let_ (callVar_eval parseProg_wellScoped (i := 0) (v := encode x) (by simp) h₂)
            (Eval.let_ (callVar_eval sndProg_wellScoped (i := 0) (v := Data.parse x) (by simp) h₃)
              (Eval.let_ (callVar_eval fstProg_wellScoped (i := 1) (v := Data.parse x) (by simp) h₄)
                (Eval.let_ (callVar_eval normBinProg_wellScoped (i := 0) (v := (Data.parse x).left)
                    (by simp) h₅)
                  (Eval.let_ (callVar_eval G.samplerProg.closed (i := 0)
                      (v := Data.normBin (Data.parse x).left) (by simp) h₆')
                    (Eval.let_ (call2_eval (wrapBuildProg_wellScoped _) (i := 0) (j := 3)
                        (a := sampD G x) (b := (Data.parse x).right) (by simp) (by simp) h₇)
                      (Eval.let_ (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                          (Eval.var_of_get (i := 7) (v := encode n) (by simp)))
                        (Eval.let_ (call2_eval freezeBuildProg_wellScoped (i := 0) (j := 2)
                            (a := kD n) (b := sampD G x) (by simp) (by simp) h₈)
                          (Eval.let_ (call2_eval freezeBuildProg_wellScoped (i := 1) (j := 2)
                              (a := kD n) (b := wD G U x) (by simp) (by simp) h₉)
                            (Eval.let_ (Eval.cons (Eval.cons
                                (Eval.var_of_get (i := 1) (v := dFreeze (kD n) (sampD G x)) (by simp))
                                (Eval.var_of_get (i := 0) (v := dFreeze (kD n) (wD G U x)) (by simp)))
                                (Eval.var_of_get (i := 11) (v := encode lam) (by simp)))
                              (callVar_eval G.compress.closed (i := 0)
                                (v := .cons (.cons (dFreeze (kD n) (sampD G x))
                                  (dFreeze (kD n) (wD G U x))) (encode lam))
                                (by simp) h₁₀')))))))))))))
  refine ⟨_, ?_, run⟩
  -- the sizes of the intermediate values
  have hs : (encode c : Data).size = esize c := rfl
  have hx : (encode x : Data).size ≤ 4 * x.length + 1 := esize_bitStr_le x
  have hp : (Data.parse x).size ≤ x.length + 1 :=
    (Data.size_parse_le x).trans (by omega)
  have hpl : (Data.parse x).left.size ≤ (Data.parse x).size := Machine.size_left_le _
  have hpr : (Data.parse x).right.size ≤ (Data.parse x).size := Machine.size_right_le _
  have hspine : (Data.parse x).left.spine ≤ (Data.parse x).left.size := Data.spine_le_size _
  have hnb : (Data.parse x).left.normBin.size ≤ (Data.parse x).left.size := Data.size_normBin_le _
  have hdl : esize (descLam x) = (Data.parse x).left.normBin.size := by
    show (encode (Data.natOf (Data.parse x).left) : Data).size = _
    rw [Data.encode_natOf]
  have ht₆' : t₆ ≤ sampBound G x.length :=
    ht₆.trans (polynomial_eval_mono _ (by rw [hdl]; omega))
  have hsamp : (sampD G x).size ≤ sampBound G x.length :=
    (G.samplerProg.esize_apply_le (descLam x)).trans (polynomial_eval_mono _ (by rw [hdl]; omega))
  have hu : (encode U.univ : Data).size = esize U.univ := rfl
  have hw : (wD G U x).size ≤ wBound G U x.length := by
    rw [wD, size_dWrapCore, hu, wBound]; omega
  have hn : (encode n : Data).size ≤ 4 * Nat.size n + 1 := esize_nat_le n
  have hk : (kD n).size = (encode n : Data).size + 4 := by
    show (Data.cons (Data.cons .nil .nil) (encode n)).size = _
    simp only [Data.size_cons, Data.size_nil]; omega
  have hkB : (kD n).size ≤ kBound n := by rw [hk, kBound]; omega
  have hfs := size_dFreeze (kD n) (sampD G x)
  have hfd := size_dFreeze (kD n) (wD G U x)
  have hF : (dFreeze (kD n) (sampD G x)).size + (dFreeze (kD n) (wD G U x)).size ≤
      fBound G U x.length n := by
    rw [hfs, hfd, fBound]; omega
  have harg : (Data.cons (Data.cons (dFreeze (kD n) (sampD G x)) (dFreeze (kD n) (wD G U x)))
      (encode lam)).size = (dFreeze (kD n) (sampD G x)).size + (dFreeze (kD n) (wD G U x)).size +
        (encode lam : Data).size + 2 := by
    simp only [Data.size_cons]; omega
  have hl : (encode lam : Data).size = esize lam := rfl
  have e1 : esize (frozen G U x n).sampler.prog = (dFreeze (kD n) (sampD G x)).size := by
    show (encode _ : Data).size = _
    rw [encode_frozen_sampler]
  have e2 : esize (frozen G U x n).decider.prog = (dFreeze (kD n) (wD G U x)).size := by
    show (encode _ : Data).size = _
    rw [encode_frozen_decider]
  have ht₁₀' : t₁₀ ≤ G.compress.timeBound.eval (fBound G U x.length n + esize lam + 2) := by
    refine ht₁₀.trans (polynomial_eval_mono _ ?_)
    rw [esize_prod, esize_prod, e1, e2]; omega
  -- the stages' costs, in the bounds
  have ht₂' : t₂ ≤ (x.length + 2) * (4 * x.length + 1 + 2 * x.length + 25) :=
    ht₂.trans (Nat.mul_le_mul_left _ (by omega))
  have ht₅' : t₅ ≤ (x.length + 3) * (x.length + 26) + 3 * (x.length + 1) + 10 :=
    ht₅.trans (by
      have : ((Data.parse x).left.spine + 2) * ((Data.parse x).left.size + 25) ≤
          (x.length + 3) * (x.length + 26) := Nat.mul_le_mul (by omega) (by omega)
      omega)
  have hwB : wBound G U x.length =
      sampBound G x.length + (x.length + 1) + 2 * esize U.univ + wrapNodes := rfl
  unfold prepBound
  omega
end MIPRE.Halting
