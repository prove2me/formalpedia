-- Prove2me | solution 1 for MIPRE.Halting.outDec_cost
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:24:43.113431+00:00
-- url     : https://prove2.me/submissions/4277fb7b-a599-4a2b-8ab7-2cf52c4197e6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorCost.lean (solution of MIPRE.Halting.outDec_cost);
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
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
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
import Definitions.Def_MIPRE_Foundations_Halting_CompressorCost
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Halting_esize_frozen_le
import Theorems.Thm_MIPRE_Halting_prepProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem call2_wellScoped {n i j : ℕ} (hi : i < n) (hj : j < n) {q : Prog} (hq : q.WellScoped 1) :
    (call2 i j q).WellScoped n :=
  ⟨⟨hi, hj⟩, hq.mono (by omega) _⟩
end MIPRE.Cost.Prog

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem prepProg_wellScoped : (prepProg G U).WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, trivial, ?_⟩
  refine ⟨callVar_wellScoped (by decide) (readProg_wellScoped U.closed), ?_⟩
  refine ⟨callVar_wellScoped (by decide) parseProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) sndProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) fstProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) normBinProg_wellScoped, ?_⟩
  refine ⟨callVar_wellScoped (by decide) G.samplerProg.closed, ?_⟩
  refine ⟨call2_wellScoped (by decide) (by decide) (wrapBuildProg_wellScoped _), ?_⟩
  refine ⟨⟨⟨trivial, trivial⟩, by simp [WellScoped]⟩, ?_⟩
  refine ⟨call2_wellScoped (by decide) (by decide) freezeBuildProg_wellScoped, ?_⟩
  refine ⟨call2_wellScoped (by decide) (by decide) freezeBuildProg_wellScoped, ?_⟩
  refine ⟨by simp [WellScoped], ?_⟩
  exact callVar_wellScoped (by decide) G.compress.closed
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem haltProg_wellScoped : (haltProg G U).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, callVar_wellScoped (by decide) (prepProg_wellScoped G U),
    ⟨⟨by simp [WellScoped], by simp [WellScoped]⟩, callVar_wellScoped (by decide) U.closed⟩⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The run of the preparation, as the decider calls it, with the size of what it produces. -/
theorem prep_call {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ)
    (d : Data) : ∃ t ≤ prepBound G U (esize c) n x.length (esize lam),
      (compressedD G U x n lam).size ≤ t ∧
      Eval [encode (c, n, lam), d, .cons (encode (c, n, lam)) d] (callVar 0 (prepProg G U))
        (compressedD G U x n lam) ((encode (c, n, lam) : Data).size + 1 + t + 1) := by
  obtain ⟨t, ht, h⟩ := prepProg_runs G U hsd lam
  exact ⟨t, ht, h.size_le, callVar_eval (prepProg_wellScoped G U) (i := 0)
    (v := encode (c, n, lam)) (by simp) h⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The pairing step of the decider. -/
theorem pair_step (P d cmpD : Data) :
    Eval [cmpD, P, d, .cons P d] (.cons (.var 0) (.var 2)) (.cons cmpD d)
      (cmpD.size + 1 + (d.size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := cmpD) (by simp))
    (Eval.var_of_get (i := 2) (v := d) (by simp))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- **Forward run.** A run of the universal machine on the compressed decider's description and
the input is a run of the decider, at the cost of the preparation and the copies. -/
theorem haltProg_runs {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ)
    {d r : Data} {t : ℕ} (h : U.univ.Runs (.cons (compressedD G U x n lam) d) r t) :
    ∃ t' ≤ 3 * prepBound G U (esize c) n x.length (esize lam) + esize (c, n, lam) +
        2 * d.size + t + 12,
      (haltProg G U).Runs (.cons (encode (c, n, lam)) d) r t' := by
  obtain ⟨tp, htp, hsz, hp⟩ := prep_call G U hsd lam d
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons (encode (c, n, lam)) d]) (i := 0)
    (a := encode (c, n, lam)) (b := d) (by simp)
    (Eval.let_ hp (Eval.let_ (pair_step (encode (c, n, lam)) d (compressedD G U x n lam))
      (callVar_eval U.closed (i := 0) (v := .cons (compressedD G U x n lam) d) (by simp) h)))⟩
  have he : (encode (c, n, lam) : Data).size = esize (c, n, lam) := rfl
  simp only [Data.size_cons]
  omega
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam m : ℕ)
    (d : Data) :
    ∃ r t, t ≤ innerBound G U (esize c) n x.length lam (esize lam) m d.size ∧
      (outDec G U c n lam).Runs (.cons (encode m) d) r t := by
  obtain ⟨r, t₁, ht₁, h₁⟩ := G.decider_time
    ((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog) lam m d
  rw [G.output_decider] at h₁
  obtain ⟨t₂, ht₂, h₂⟩ := U.time_le _ _ _ _ h₁
  obtain ⟨t₃, ht₃, h₃⟩ := haltProg_runs G U hsd lam (d := .cons (encode m) d) h₂
  refine ⟨r, _, ?_, hardcode_time (haltProg_wellScoped G U) h₃⟩
  -- the sizes
  have hcmp : esize (G.compress (((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog),
      lam)) ≤ G.compress.timeBound.eval (fBound G U x.length n + esize lam + 2) := by
    refine (G.compress.esize_apply_le _).trans (polynomial_eval_mono _ ?_)
    have := esize_frozen_le G U x n
    simp only [esize_prod]; omega
  have hP : (encode (c, n, lam) : Data).size = esize c + (esize n + esize lam + 1) + 1 := rfl
  have hP' : esize (c, n, lam) = esize c + (esize n + esize lam + 1) + 1 := rfl
  have hin : (Data.cons (encode m) d).size = esize m + d.size + 1 := rfl
  have hm : esize m ≤ 4 * Nat.size m + 1 := esize_nat_le m
  have hn : esize n ≤ 4 * Nat.size n + 1 := esize_nat_le n
  have ht₂' : t₂ ≤ U.bound.eval (G.compress.timeBound.eval (fBound G U x.length n + esize lam + 2) +
      ((4 * Nat.size m + 1) + d.size + 1) + G.bound.eval (m + lam) * (d.size + 1) ^ G.deg) :=
    ht₂.trans (polynomial_eval_mono _ (by rw [hin]; omega))
  simp only [innerBound]
  omega
end MIPRE.Halting
