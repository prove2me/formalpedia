-- Prove2me | solution 1 for MIPRE.Halting.exists_compressorSpec
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:31:43.984515+00:00
-- url     : https://prove2.me/submissions/4cfbdb18-044b-4d33-9f12-e6d1e6a74ae6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorCost.lean (solution of MIPRE.Halting.exists_compressorSpec);
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
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev
import Theorems.Thm_MIPRE_Halting_decider_clause
import Theorems.Thm_MIPRE_Halting_esize_wrapCore_le
import Theorems.Thm_MIPRE_Halting_exists_ansBound_le
import Theorems.Thm_MIPRE_Halting_haltProg_runs_inv
import Theorems.Thm_MIPRE_Halting_lamOf_ge
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

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- **Acceptance agreement of the decider.** On a succinct description `(c, n)` of `x`, the
decider with `(c, n, λ)` in front accepts `(m, x', y', a, b)` exactly when the compressed
decider of the verifier of `x` frozen at `2n + 1`, at parameter `λ`, accepts it. -/
theorem haltProg_accepts_iff {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x)
    (lam m : ℕ) (x' y' a b : BitStr) :
    (∃ t, (haltProg G U).Runs (.cons (encode (c, n, lam)) (encode (m, x', y', a, b)))
        (encode true) t) ↔
      (G.output ((frozen G U x n).sampler.prog, (frozen G U x n).decider.prog) lam).decider.Accepts
        m x' y' a b := by
  rw [Decider.Accepts, G.output_decider]
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t', h'⟩ := haltProg_runs_inv G U hsd lam h
    exact U.halts_of _ _ _ _ h'
  · rintro ⟨t, h⟩
    obtain ⟨t', -, h'⟩ := U.time_le _ _ _ t h
    obtain ⟨t'', -, h''⟩ := haltProg_runs G U hsd lam h'
    exact ⟨t'', h''⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The verifier the output denotes: the compressed sampler at `λ`, and the hardcoded decider
as a program. -/
theorem Vof_comprStr (c : Prog) (n lam : ℕ) :
    Vof G U (comprStr G U c n lam) =
      Verifier.ofSamplerDecider U (G.sampler lam) (hardcode (haltProg G U) (encode (c, n, lam))) := by
  rw [Vof, comprStr, descLam_descOf, descDecD_descOf]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- **The acceptance agreement of the output** (the field `CompressorSpec.accepts_compr`): on a
succinct description `(c, n)` of `x`, the decider of the verifier the output denotes accepts, at
every index, exactly what the compressed decider of the verifier of `x` frozen at `2n + 1`
accepts. -/
theorem comprStr_accepts {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x)
    (lam m : ℕ) (x' y' a b : BitStr) :
    (Vof G U (comprStr G U c n lam)).decider.Accepts m x' y' a b ↔
      (G.output (((Vof G U x).freeze (2 * n + 1)).sampler.prog,
        ((Vof G U x).freeze (2 * n + 1)).decider.prog) lam).decider.Accepts m x' y' a b := by
  rw [Vof_comprStr, Verifier.ofSamplerDecider_accepts]
  constructor
  · rintro ⟨-, -, t, h⟩
    obtain ⟨t', -, h'⟩ := hardcode_time_rev (haltProg_wellScoped G U) h
    exact (haltProg_accepts_iff G U hsd lam m x' y' a b).1 ⟨t', h'⟩
  · intro h
    have hlen := (G.output _ lam).accepts_length m x' y' a b h
    rw [G.output_sampler] at hlen
    obtain ⟨t, ht⟩ := (haltProg_accepts_iff G U hsd lam m x' y' a b).2 h
    exact ⟨hlen.1, hlen.2, _, hardcode_time (haltProg_wellScoped G U) ht⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_lamOf : PolyBounded lamOf :=
  (PolyBounded.two_pow_size 0 2).mono fun n => by simp [lamOf]
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- `λ(n) ≥ (n + 1) ^ 2`. -/
theorem sq_le_lamOf (n : ℕ) : (n + 1) ^ 2 ≤ lamOf n := by
  rw [lamOf, Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_size_self n) 2
end MIPRE.Halting

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
theorem Vof_comprStr' (c : Prog) (n lam : ℕ) :
    Vof G U (comprStr G U c n lam) = Verifier.ofSamplerDecider U (G.sampler lam) (outDec G U c n lam) :=
  Vof_comprStr G U c n lam
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_sampZ : PolyBounded (sampZ G) :=
  PolyBounded.eval _ (PolyBounded.id.add polyBounded_lamOf)
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
/-- **The sampler clauses**: past a threshold, at every index `m ≥ 2` the compressed sampler at
`λ(n)` has dimension at most `m ^ n` and runs within `m ^ n · (|d| + 1) ^ n`. -/
theorem sampler_clauses : ∃ n₀, ∀ n, n₀ ≤ n → ∀ m, 2 ≤ m →
    (G.sampler (lamOf n)).dim m ≤ m ^ n ∧ (G.sampler (lamOf n)).TimeBoundAt m (m ^ n) n := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_sampZ G).absorb
  refine ⟨max n₀ G.deg, fun n hn m hm => ?_⟩
  have h1 : G.bound.eval (m + lamOf n) ≤ m ^ n := by
    have := hn₀ n (le_trans (le_max_left _ _) hn) m hm 1 le_rfl
    rw [one_pow, mul_one, mul_one] at this
    exact (bound_le_sampZ G (by omega) (by omega)).trans this
  exact ⟨(G.sampler_dim _ m).trans h1,
    (G.sampler_time (lamOf n) m).mono h1 (le_trans (le_max_right _ _) hn)⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_sizeZ : PolyBounded (sizeZ G U) :=
  ((PolyBounded.eval _ ((PolyBounded.id.const_mul 8).add_const 5)).add
    (PolyBounded.id.const_mul 12)).add_const _
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

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- **The size clause**: past a threshold, a description of size at most `n / 2` yields an
output whose verifier has size at most `n`. -/
theorem size_clause : ∃ n₀, ∀ n, n₀ ≤ n → ∀ c : Prog, 2 * esize c ≤ n →
    (Vof G U (comprStr G U c n (lamOf n))).size ≤ n := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_sizeZ G U).absorb_log 0 1
  refine ⟨n₀, fun n hn c hc => ?_⟩
  have h := hn₀ n hn
  simp only [Nat.zero_add, Nat.one_mul] at h
  rw [Vof_comprStr', Verifier.size]
  refine max_le ?_ ?_
  · exact (esize_sampler_le G n).trans (by simp only [sizeZ] at h ⊢; omega)
  · exact (esize_wrapCore_le G U c n).trans (by omega)
end MIPRE.Halting

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- **The field `isBounded_compr`.** -/
theorem isBounded_comprStr : ∃ n₀, ∀ n, n₀ ≤ n → ∀ (c : Prog) (x : BitStr), 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
    (Vof G U (comprStr G U c n (lamOf n))).IsBounded n := by
  obtain ⟨nS, hS⟩ := sampler_clauses G
  obtain ⟨nZ, hZ⟩ := size_clause G U
  obtain ⟨nD, hD⟩ := decider_clause G U
  refine ⟨max nS (max nZ nD), fun n hn c x hc hsd hx => ⟨fun m hm => ?_, ?_⟩⟩
  · have h1 := hS n (by omega) m hm
    have h2 := hD n (by omega) c x hc hsd hx m hm
    refine ⟨?_, ?_, h2⟩
    · rw [Vof_comprStr']; exact h1.1
    · rw [Vof_comprStr']; exact h1.2
  · exact hZ n (by omega) c hc
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- **The field `ansBound_le`**, from `exists_ansBound_le` at `λ(n) ≥ n + 1`. -/
theorem ansBound_le_lamOf : ∃ n₀, ∀ (x : BitStr) (n : ℕ), n₀ ≤ n → x.length ≤ n + 1 →
    ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lamOf n := by
  obtain ⟨lam₀, n₀, h⟩ := exists_ansBound_le G
  refine ⟨max lam₀ n₀, fun x n hn hx => h x (lamOf n) n ?_ (le_trans (le_max_right _ _) hn) hx⟩
  have := sq_le_lamOf n
  have := le_trans (le_max_left _ _) hn
  nlinarith
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution (compr : PolyTimeFun (Prog × ℕ) BitStr)
    (hcompr : ∀ (c : Prog) (n : ℕ), compr (c, n) = comprStr G U c n (lamOf n)) :
    ∃ S : CompressorSpec G U, S.compr = compr ∧ S.lam = lamOf := by
  obtain ⟨nB, hB⟩ := isBounded_comprStr G U
  obtain ⟨nL, hL⟩ := lamOf_ge
  obtain ⟨nA, hA⟩ := ansBound_le_lamOf G
  refine ⟨{
    n₀ := max G.C₀ (max nB (max nL nA))
    C₀_le := le_max_left _ _
    compr := compr
    lam := lamOf
    descLam_compr := fun c n => by rw [hcompr]; exact descLam_comprStr G U c n _
    accepts_compr := fun c x n _ _ hsd _ m x' y' a b => by
      rw [hcompr]; exact comprStr_accepts G U hsd (lamOf n) m x' y' a b
    isBounded_compr := fun c x n hn hc hsd hx _ => by
      rw [hcompr]
      exact hB n (by omega) c x hc hsd hx
    lam_ge := fun n hn => hL n (by omega)
    ansBound_le := fun x n hn hx => hA x n (by omega) hx },
    rfl, rfl⟩
end MIPRE.Halting
