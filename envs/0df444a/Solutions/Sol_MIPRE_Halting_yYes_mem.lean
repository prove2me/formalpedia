-- Prove2me | solution 1 for MIPRE.Halting.yYes_mem
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:54:34.493979+00:00
-- url     : https://prove2.me/submissions/69202b38-1e2a-46a1-a9f8-9575843c993e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Strings.lean (solution of MIPRE.Halting.yYes_mem);
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Theorems.Thm_MIPRE_Cost_Prog_wrapCore_hasPolyCost
import Theorems.Thm_MIPRE_Halting_decYes_halts
import Theorems.Thm_MIPRE_Halting_decYes_runs_true_iff
import Theorems.Thm_MIPRE_Verifier_exists_isBounded_lam
import Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_accepts_diagonal

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A verifier that is `n`-bounded, rejects long answers, and accepts a constant answer
everywhere is in the class `A`. -/
theorem inClassA_of_accepts_diagonal {n T : ℕ} (hb : V.IsBounded n) (hrej : V.RejectsLong n T)
    (a₀ : Answers T)
    (hacc : ∀ x y : V.Questions n, V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1) :
    V.InClassA n T :=
  ⟨hb, hrej, V.hasPerfectPCC_of_accepts_diagonal a₀ hacc⟩
end MIPRE.Verifier

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

namespace MIPRE.Verifier
open Cost
/-- `λ`-boundedness is monotone in `λ`: every clause of `def:lambda-bounded` weakens as `λ`
grows. Raising `λ` is free, which is what lets a verifier bounded at some fixed `λ` belong to
the classes at every level above it. -/
theorem IsBounded.mono {ℓ : ℕ} {V : Verifier ℓ} {lam lam' : ℕ} (h : V.IsBounded lam)
    (hle : lam ≤ lam') : V.IsBounded lam' := by
  obtain ⟨hmain, hsize⟩ := h
  refine ⟨fun n hn => ?_, hsize.trans hle⟩
  obtain ⟨hdim, hS, hD⟩ := hmain n hn
  have hpow : n ^ lam ≤ n ^ lam' := Nat.pow_le_pow_right (by omega) hle
  exact ⟨hdim.trans hpow, hS.mono hpow hle, hD.mono hpow hle⟩
end MIPRE.Verifier

namespace MIPRE
open Cost
/-- A uniform time bound whose coefficient is polynomially bounded *is* polynomially bounded
cost. This is the direction `MIPRE.GapCompression` supplies: its `sampler_time` and
`decider_time` fields bound the running times of the compressed verifier by
`bound.eval (n + λ)` at a fixed degree, and `bound.eval (n + λ)` is polynomially bounded in
`n`. -/
theorem Cost.Prog.hasPolyCost_of_bound {p : Prog} {T : ℕ → ℕ} {k : ℕ} (hT : PolyBounded T)
    (h : ∀ (n : ℕ) (d : Data), HaltsWithin p (.cons (encode n) d) (T n * (d.size + 1) ^ k)) :
    p.HasPolyCost :=
  ⟨T, k, hT, fun n d => h n d⟩
end MIPRE

namespace MIPRE
open Cost
/-- The sampler form. -/
theorem CL.Sampler.hasPolyCost_of_timeBound {ℓ : ℕ} {S : CL.Sampler ℓ} {T : ℕ → ℕ} {k : ℕ}
    (hT : PolyBounded T) (h : ∀ n, S.TimeBoundAt n (T n) k) : S.prog.HasPolyCost :=
  Cost.Prog.hasPolyCost_of_bound hT fun n d => h n d
end MIPRE

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **The threshold form**: such a verifier is `n`-bounded at every level `n` from some `n₀` on.
This is the shape the classes `MIPRE.Halting.classA`, `classB` consume, `IsBounded n` being
asked at the level itself. -/
theorem exists_isBounded (hdim : PolyBounded V.sampler.dim)
    (hS : V.sampler.prog.HasPolyCost) (hD : V.decider.prog.HasPolyCost) :
    ∃ n₀, ∀ n, n₀ ≤ n → V.IsBounded n := by
  obtain ⟨lam, hlam⟩ := V.exists_isBounded_lam hdim hS hD
  exact ⟨lam, fun _ hn => hlam.mono hn⟩
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open Cost.Prog
/-- **The verifier a string denotes is `λ`-bounded**, at every level from some `n₀` on,
provided the sampler and the string's own decider have polynomially bounded cost and the
sampler's dimension is polynomially bounded. This is what inhabits `Verifier.IsBounded`. -/
theorem ofSamplerDecider_isBounded {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ)
    (dec : Prog) (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim)
    (hdec : dec.HasPolyCost) :
    ∃ n₀, ∀ n, n₀ ≤ n → (ofSamplerDecider U S dec).IsBounded n :=
  (ofSamplerDecider U S dec).exists_isBounded hdim hS
    (wrapCore_hasPolyCost U S dec hS hdim hdec)
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost
theorem decYes_hasPolyCost : decYes.HasPolyCost :=
  ⟨fun _ => 10, 0, PolyBounded.const 10, fun n d =>
    let ⟨r, t, ht, hr⟩ := decYes_halts (.cons (encode n) d); ⟨r, t, by simpa using ht, hr⟩⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
variable (G : GapCompression) (U : UniversalMachine)
/-- The compressed sampler's cost is polynomially bounded: its time bound is
`bound (n + λ)` at the fixed degree `deg` (`GapCompression.sampler_time`). -/
theorem sampler_hasPolyCost (lam : ℕ) : (G.sampler lam).prog.HasPolyCost :=
  CL.Sampler.hasPolyCost_of_timeBound (T := fun n => G.bound.eval (n + lam)) (k := G.deg)
    (PolyBounded.eval G.bound (PolyBounded.id.add_const lam)) fun n => G.sampler_time lam n
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
variable (G : GapCompression) (U : UniversalMachine)
/-- Its dimension is polynomially bounded (`GapCompression.sampler_dim`). -/
theorem sampler_polyBounded_dim (lam : ℕ) : PolyBounded (G.sampler lam).dim :=
  (PolyBounded.eval G.bound (PolyBounded.id.add_const lam)).mono (G.sampler_dim lam)
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution : ∃ n₀, ∀ n, n₀ ≤ n → yYes ∈ classA G U n := by
  obtain ⟨n₀, hn₀⟩ := Verifier.ofSamplerDecider_isBounded U (G.sampler 0) decYes
    (sampler_hasPolyCost G 0) (sampler_polyBounded_dim G 0) decYes_hasPolyCost
  refine ⟨n₀, fun n hn => ?_⟩
  show (Vof G U yYes).InClassA n (ansBound G yYes n)
  rw [Vof_yYes]
  refine Verifier.inClassA_of_accepts_diagonal _ (hn₀ n hn) ?_
    (⟨[], by simp⟩ : Verifier.Answers (ansBound G yYes n)) fun p q => ?_
  · -- only the empty answers are accepted, so every long one is rejected
    intro x y a b hlen hacc
    rw [Verifier.ofSamplerDecider_accepts] at hacc
    obtain ⟨-, -, hrun⟩ := hacc
    obtain ⟨rfl, rfl⟩ := (decYes_runs_true_iff n x y a b).1 hrun
    simp at hlen
  · rw [Verifier.ofSamplerDecider_accepts]
    exact ⟨CL.length_toBits p, CL.length_toBits q, (decYes_runs_true_iff n _ _ [] []).2 ⟨rfl, rfl⟩⟩
end MIPRE.Halting
