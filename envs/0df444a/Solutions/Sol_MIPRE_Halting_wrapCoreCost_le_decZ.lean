-- Prove2me | solution 1 for MIPRE.Halting.wrapCoreCost_le_decZ
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:26:28.439995+00:00
-- url     : https://prove2.me/submissions/f2deafaf-2174-4db7-a423-f83cc74ad10d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorCost.lean (solution of MIPRE.Halting.wrapCoreCost_le_decZ);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- `λ(n)` is monotone. -/
theorem lamOf_mono {n n' : ℕ} (h : n ≤ n') : lamOf n ≤ lamOf n' :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.size_le_size h))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem bound_le_sampZ {m n z : ℕ} (hm : m ≤ z) (hn : n ≤ z) :
    G.bound.eval (m + lamOf n) ≤ sampZ G z :=
  polynomial_eval_mono _ (Nat.add_le_add hm (lamOf_mono hn))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The compressed sampler's program at `λ(n)` has size polynomial in `size n`. -/
theorem esize_sampler_le (n : ℕ) :
    esize (G.sampler (lamOf n)).prog ≤ G.samplerProg.timeBound.eval (8 * Nat.size n + 5) := by
  rw [← G.samplerProg_eq]
  exact (G.samplerProg.esize_apply_le (lamOf n)).trans
    (polynomial_eval_mono _ (esize_lamOf_le n))
end MIPRE.Halting

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem readIter_mono {s s' n n' L L' : ℕ} (hs : s ≤ s') (hn : n ≤ n') (hL : L ≤ L') :
    readIter U s n L ≤ readIter U s' n' L' := by
  unfold readIter; gcongr
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem sampBound_mono {L L' : ℕ} (hL : L ≤ L') : sampBound G L ≤ sampBound G L' :=
  polynomial_eval_mono _ (by omega)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem wBound_mono {L L' : ℕ} (hL : L ≤ L') : wBound G U L ≤ wBound G U L' := by
  unfold wBound; have := sampBound_mono G hL; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem kBound_mono {n n' : ℕ} (hn : n ≤ n') : kBound n ≤ kBound n' := by
  unfold kBound; have := Nat.size_le_size hn; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem fBound_mono {L L' n n' : ℕ} (hL : L ≤ L') (hn : n ≤ n') :
    fBound G U L n ≤ fBound G U L' n' := by
  unfold fBound
  have := sampBound_mono G hL; have := wBound_mono G U hL; have := kBound_mono hn; omega
end MIPRE.Halting

attribute [local gcongr] MIPRE.Halting.readIter_mono MIPRE.Halting.sampBound_mono MIPRE.Halting.wBound_mono MIPRE.Halting.kBound_mono MIPRE.Halting.fBound_mono

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem prepBound_mono {s s' n n' L L' l l' : ℕ} (hs : s ≤ s') (hn : n ≤ n') (hL : L ≤ L')
    (hl : l ≤ l') : prepBound G U s n L l ≤ prepBound G U s' n' L' l' := by
  unfold prepBound; gcongr
end MIPRE.Halting

attribute [local gcongr] MIPRE.Halting.prepBound_mono

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem innerBound_mono {s s' n n' L L' lam lam' l l' m m' t t' : ℕ} (hs : s ≤ s') (hn : n ≤ n')
    (hL : L ≤ L') (hlam : lam ≤ lam') (hl : l ≤ l') (hm : m ≤ m') (ht : t ≤ t') :
    innerBound G U s n L lam l m t ≤ innerBound G U s' n' L' lam' l' m' t' := by
  unfold innerBound; gcongr
end MIPRE.Halting

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size MIPRE.Halting.innerBound_mono

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution {c : Prog} {x : BitStr} {n m t z : ℕ} (hc : esize c ≤ n)
    (hx : x.length ≤ n + 1) (hm : m ≤ z) (hn : n ≤ z) (ht : t ≤ z) :
    wrapCoreCost U (G.sampler (lamOf n)) (outDec G U c n (lamOf n))
        (fun m => G.bound.eval (m + lamOf n)) G.deg m
        (innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m t) t ≤ decZ G U z := by
  -- the atoms
  have hσ : esize (G.sampler (lamOf n)).prog ≤ sigZ G z :=
    (esize_sampler_le G n).trans (polynomial_eval_mono _ (by have := Nat.size_le_size hn; omega))
  have hem : esize m ≤ 4 * Nat.size z + 1 :=
    (esize_nat_le m).trans (by have := Nat.size_le_size hm; omega)
  have hen : esize n ≤ 4 * Nat.size z + 1 :=
    (esize_nat_le n).trans (by have := Nat.size_le_size hn; omega)
  have hel : esize (lamOf n) ≤ 8 * Nat.size z + 5 :=
    (esize_lamOf_le n).trans (by have := Nat.size_le_size hn; omega)
  have hβ : G.bound.eval (m + lamOf n) ≤ sampZ G z := bound_le_sampZ G hm hn
  have hdim : (G.sampler (lamOf n)).dim m ≤ sampZ G z := (G.sampler_dim _ m).trans hβ
  have hedim : esize ((G.sampler (lamOf n)).dim m) ≤ 4 * sampZ G z + 1 :=
    (esize_nat_le _).trans (by
      have := Nat.size_le.2 (Nat.lt_two_pow_self (n := (G.sampler (lamOf n)).dim m)); omega)
  have hsdim : Nat.size ((G.sampler (lamOf n)).dim m) ≤ sampZ G z :=
    (Nat.size_le.2 (Nat.lt_two_pow_self)).trans hdim
  have hδ : esize (outDec G U c n (lamOf n)) ≤ deltaZ G U z := by
    rw [esize_outDec, deltaZ]; omega
  have hι : innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m t ≤ iotaZ G U z :=
    innerBound_mono G U (by omega) hn (by omega) (lamOf_mono hn) hel hm ht
  have hcheck : checkCost t ((G.sampler (lamOf n)).dim m) ≤ 60 * (z + sampZ G z + 30) ^ 2 := by
    unfold checkCost; gcongr
  have hhead : wrapHeadZ U (G.sampler (lamOf n)) (fun m => G.bound.eval (m + lamOf n)) G.deg m ≤
      headZ G U z := by
    unfold wrapHeadZ headZ; gcongr
  unfold wrapCoreCost decZ
  gcongr
end MIPRE.Halting
