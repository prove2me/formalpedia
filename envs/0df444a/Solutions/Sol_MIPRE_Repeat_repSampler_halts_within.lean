-- Prove2me | solution 1 for MIPRE.Repeat.repSampler_halts_within
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:55:21.465658+00:00
-- url     : https://prove2.me/submissions/8e62263a-b23a-4bec-af86-3a91f3f29aaa

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/SamplerCost.lean (solution of MIPRE.Repeat.repSampler_halts_within);
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
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Repeat_block_calls_time

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
/-- The size of the encoded dimension query. -/
theorem size_encode_dimension : (encode CL.Sampler.Query.dimension : Data).size = 9 := rfl
end
end MIPRE.Cost.Prog

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
/-- The time of the dimension query through the universal machine. -/
theorem dim_call_time (hS : S.TimeBoundAt n R.S R.k) :
    ∃ td, td ≤ selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k) ∧
      Eval [Data.cons (encode S.prog) (.cons (encode n) (encode CL.Sampler.Query.dimension))]
        selfUniversal.univ (encode (S.dim n)) td := by
  obtain ⟨t, h⟩ := S.runs_dimension n
  obtain ⟨r', t', ht', h'⟩ := hS (encode CL.Sampler.Query.dimension)
  obtain ⟨rfl, rfl⟩ := h.deterministic h'
  obtain ⟨t'', ht'', h''⟩ := selfUniversal.time_le _ _ _ _ h
  refine ⟨t'', ht''.trans (polynomial_eval_mono _ ?_), h''⟩
  have hd : (encode (n, CL.Sampler.Query.dimension) : Data).size = esize n + 9 + 1 := rfl
  simp only [size_encode_dimension, show (9 : ℕ) + 1 = 10 from rfl] at ht'
  rw [hd]
  omega
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
theorem _root_.solution (hS : S.TimeBoundAt n R.S R.k) (d : Data) :
    ∃ r t, t ≤ anyCost lam tau n (encode S.prog) (S.dim n) d.size
        (selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k))
        (selfUniversal.bound.eval (esize S.prog + (esize n + d.size + 1) + R.S * (d.size + 1) ^ R.k)) +
        (esize S.prog + esize lam + esize tau + 2) + (esize n + d.size + 1) + 3 ∧
      (repSamplerProg S.prog lam tau).Runs (.cons (encode n) d) r t := by
  obtain ⟨td, htd, hdim⟩ := dim_call_time S n R hS
  obtain ⟨fq, hfq⟩ := block_calls_time S n R hS d
  set Tu := selfUniversal.bound.eval (esize S.prog + (esize n + d.size + 1) + R.S * (d.size + 1) ^ R.k)
    with hTu
  obtain ⟨r, t, ht, run⟩ := repSampCore_runs_any selfUniversal.closed (encode S.prog) lam tau n
    (S.dim n) d hdim fq Tu hfq
  refine ⟨r, _, ?_, repSamplerProg_runs S.prog lam tau n d run⟩
  have hmono : anyCost lam tau n (encode S.prog) (S.dim n) d.size td Tu ≤
      anyCost lam tau n (encode S.prog) (S.dim n) d.size
        (selfUniversal.bound.eval (esize S.prog + (esize n + 10) + R.S * 10 ^ R.k)) Tu := by
    unfold anyCost
    omega
  have hP : (encode (S.prog, lam, tau) : Data).size = esize S.prog + esize lam + esize tau + 2 := by
    simp only [encode_prod, size_cons, esize]; omega
  have hin : (Data.cons (encode n) d).size = esize n + d.size + 1 := by
    simp only [size_cons, esize]
  rw [hP, hin]
  omega
end MIPRE.Repeat
