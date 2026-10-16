-- Prove2me | solution 1 for MIPRE.Halting.sampProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:21:02.732534+00:00
-- url     : https://prove2.me/submissions/62eb6620-1585-47c1-a1fb-80034e6b21ea

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassVerifier.lean (solution of MIPRE.Halting.sampProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
open Polynomial
theorem seq_runs {p q : Prog} (hq : q.WellScoped 1) {x y r : Data} {t₁ t₂ : ℕ}
    (hp : p.Runs x y t₁) (hq' : q.Runs y r t₂) :
    (seq p q).Runs x r (t₁ + (y.size + 1 + t₂ + 1) + 1) :=
  Eval.let_ hp (callVar_eval (env := [y, x]) (i := 0) hq (v := y) (by simp) hq')
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
theorem runUK_runs {univ : Prog} (hU : univ.WellScoped 1) {A B r : Data} {t : ℕ}
    (h : univ.Runs A r t) :
    ∃ t' ≤ A.size + B.size + r.size + t + 8, (runUK univ).Runs (.cons A B) (.cons B r) t' := by
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons A B]) (i := 0) (n := .nil) (by simp)
    (Eval.let_ (callVar_eval (env := [A, B, .cons A B]) (i := 0) hU (v := A) (by simp) h)
      (Eval.cons (Eval.var_of_get (env := [r, A, B, .cons A B]) (i := 2) (v := B) (by simp))
        (Eval.var_of_get (env := [r, A, B, .cons A B]) (i := 0) (v := r) (by simp))))⟩
  omega
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
theorem unaryStage_runs (S : Data) (n : ℕ) :
    ∃ t ≤ S.size + esize n +
        (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90) + 5,
      unaryStage.Runs (.cons S (encode n)) (.cons S (Data.ofNat n)) t := by
  obtain ⟨t, ht, h⟩ := toUnaryProg_runs n
  refine ⟨_, ?_, Eval.elim_cons (env := [Data.cons S (encode n)]) (i := 0) (n := .nil) (by simp)
    (Eval.cons (Eval.var_of_get (env := [S, encode n, .cons S (encode n)]) (i := 0) (v := S)
        (by simp))
      (callVar_eval (env := [S, encode n, .cons S (encode n)]) (i := 1)
        toUnaryProg_wellScoped (v := encode n) (by simp) h))⟩
  have : (encode n : Data).size = esize n := rfl
  omega
end MIPRE.Cost.Prog

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem spF_apply (z r : BitStr) : spF G Λ₀ R (z, r) = (Sz G Λ₀ R z).prog := by
  show G.samplerProg (lamF Λ₀ (R z)) = _
  rw [lamF_apply, G.samplerProg_eq]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem A1_apply (z r : BitStr) :
    A1 G Λ₀ R (z, r) = (((Sz G Λ₀ R z).prog, qdim G), ((Sz G Λ₀ R z).prog, r)) := by
  show ((spF G Λ₀ R (z, r), qdim G), (spF G Λ₀ R (z, r), r)) = _
  rw [spF_apply]
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem A2_apply (sp : Prog) (r : BitStr) (u : Unary) :
    A2 G ((sp, r), u) = ((sp, encode (C G, Sampler.Query.marginal .alice 7 (r.take u.length))),
      (sp, r.take u.length)) := rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem A3_apply (sp : Prog) (z' x : BitStr) :
    A3 G ((sp, z'), x) = ((sp, encode (C G, Sampler.Query.marginal .bob 7 z')), x) := rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
/-- A run of the sampler on a query is within its time bound. -/
theorem sampler_run_bounded (S : Sampler 7) {n T k : ℕ} (hb : S.TimeBoundAt n T k)
    (q : Sampler.Query) {r : Data} {t : ℕ} (h : S.prog.Runs (encode (n, q)) r t) :
    ∃ t' ≤ T * ((encode q : Data).size + 1) ^ k, S.prog.Runs (encode (n, q)) r t' := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb (encode q)
  have h₀' : S.prog.Runs (encode (n, q)) r₀ t₀ := h₀
  obtain ⟨rfl, -⟩ := Eval.deterministic h₀' h
  exact ⟨t₀, ht₀, h₀'⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem unCost_le {d D : ℕ} (hd : d ≤ D) :
    (Nat.size d + 2) * ((d + 1) * (4 * d + 14) + 7 * esize d + 8 * d + 90) ≤ unB D := by
  have h1 : Nat.size d ≤ D := (Nat.size_le.2 Nat.lt_two_pow_self).trans hd
  have h2 : esize d ≤ 4 * D + 1 := (esize_nat_le_self d).trans (by omega)
  unfold unB
  exact Nat.mul_le_mul (by omega) (by nlinarith)
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem _root_.solution (z r : BitStr) (hd : dimz G Λ₀ R z ≤ r.length) :
    ∃ t, t ≤ sampB G U Λ₀ R (z.length + r.length) ∧
      (sampProg G U Λ₀ R).Runs (encode (z, r))
        (encode (qOf G Λ₀ R .alice z r, qOf G Λ₀ R .bob z r)) t := by
  set S := Sz G Λ₀ R z with hS
  set d := dimz G Λ₀ R z with hd_def
  set m := z.length + r.length with hm
  set z' := r.take d with hz'
  have hz'l : z'.length = d := by rw [hz', List.length_take]; omega
  have hbS : S.TimeBoundAt (C G) (G.bound.eval (C G + lamz Λ₀ R z)) G.deg :=
    G.sampler_time _ (C G)
  have hdimB : G.bound.eval (C G + lamz Λ₀ R z) ≤ dimB G Λ₀ R m :=
    polynomial_eval_mono _ (by have := lamz_le Λ₀ R z m (by omega); omega)
  have hdB : d ≤ dimB G Λ₀ R m := dimz_le G Λ₀ R z m (by omega)
  have hed : esize d ≤ 4 * dimB G Λ₀ R m + 1 := (esize_nat_le_self d).trans (by omega)
  have hed' : (encode d : Data).size = esize d := rfl
  -- stage 1
  obtain ⟨t₁, ht₁, h₁⟩ := (A1 G Λ₀ R).computes (z, r)
  rw [A1_apply, ← hS] at h₁
  have hT1 : t₁ ≤ T1B G Λ₀ R m := by
    refine ht₁.trans (polynomial_eval_mono _ ?_)
    have := esize_bitStr_le z; have := esize_bitStr_le r
    simp only [esize_prod]; omega
  have hy₁ := h₁.size_le
  -- the dimension query
  obtain ⟨t₀, hdim⟩ := S.runs_dimension (C G)
  obtain ⟨td, htd, hdim'⟩ := sampler_run_bounded S hbS _ hdim
  obtain ⟨tu₁, htu₁, hu₁⟩ := U.time_le S.prog (qdim G) (encode d) td hdim'
  obtain ⟨tk₁, htk₁, hk₁⟩ := runUK_runs U.closed (B := encode (S.prog, r)) hu₁
  have hk₁' : (runUK U.univ).Runs (encode ((S.prog, qdim G), (S.prog, r)))
    (encode ((S.prog, r), d)) tk₁ := hk₁
  have hy₂' := hk₁'.size_le
  have hsz₁ : (encode ((S.prog, qdim G), (S.prog, r)) : Data).size =
      (encode (S.prog, qdim G) : Data).size + (encode (S.prog, r) : Data).size + 1 := rfl
  have hsz₁' : (encode (S.prog, qdim G) : Data).size =
      esize S.prog + (qdim G).size + 1 := rfl
  have hqd : (encode Sampler.Query.dimension : Data).size ≤ (qdim G).size := by
    show _ ≤ (Data.cons (encode (C G)) (encode Sampler.Query.dimension)).size
    simp only [Data.size_cons]; omega
  have hsim₁ : td ≤ dimB G Λ₀ R m * (T1B G Λ₀ R m + 1) ^ G.deg :=
    htd.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hq₁ : (Data.cons (encode S.prog) (qdim G)).size = esize S.prog + (qdim G).size + 1 := rfl
  have hR1 : tk₁ ≤ R1B G U Λ₀ R m := by
    have hu := htu₁.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (qdim G).size + td ≤
        2 * T1B G Λ₀ R m + dimB G Λ₀ R m * (T1B G Λ₀ R m + 1) ^ G.deg by omega))
    unfold R1B; omega
  have hy₂ := hk₁.size_le
  -- the conversion
  obtain ⟨tn, htn, hn⟩ := unaryStage_runs (encode (S.prog, r)) d
  have e_un : (encode ((S.prog, r), unary d) : Data) =
      .cons (encode (S.prog, r)) (Data.ofNat d) := by
    show Data.cons _ (encode (unary d)) = _
    rw [encode_unary]
  have hn' : unaryStage.Runs (encode ((S.prog, r), d)) (encode ((S.prog, r), unary d)) tn := by
    rw [e_un]; exact hn
  have hy₃' := hn'.size_le
  have hUn : tn ≤ UnB G U Λ₀ R m := by
    have hsz₂ : (encode ((S.prog, r), d) : Data).size =
      (encode (S.prog, r) : Data).size + esize d + 1 := rfl
    have := unCost_le hdB
    unfold UnB; omega
  have hy₃ := hn.size_le
  -- stage 2
  obtain ⟨t₂, ht₂, h₂⟩ := (A2 G).computes ((S.prog, r), unary d)
  rw [A2_apply, length_unary, ← hz'] at h₂
  have hT2 : t₂ ≤ T2B G U Λ₀ R m := by
    refine ht₂.trans (polynomial_eval_mono _ ?_)
    have : esize ((S.prog, r), unary d) = (encode ((S.prog, r), unary d) : Data).size := rfl
    rw [this, e_un]; omega
  have hy₄ := h₂.size_le
  -- Alice's marginal
  obtain ⟨tA, hA⟩ := S.runs_marginal (C G) .alice 7 z' (by norm_num) le_rfl hz'l
  rw [CLFun.truncate_self] at hA
  obtain ⟨tA', htA', hA'⟩ := sampler_run_bounded S hbS _ hA
  obtain ⟨tu₂, htu₂, hu₂⟩ := U.time_le S.prog _ _ tA' hA'
  have hu₂' : U.univ.Runs
    (.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .alice 7 z')))
    (encode (qOf G Λ₀ R .alice z r)) tu₂ := hu₂
  obtain ⟨tk₂, htk₂, hk₂⟩ := runUK_runs U.closed (B := encode (S.prog, z')) hu₂'
  have hk₂' : (runUK U.univ).Runs
      (encode ((S.prog, encode (C G, Sampler.Query.marginal .alice 7 z')), (S.prog, z')))
      (encode ((S.prog, z'), qOf G Λ₀ R .alice z r)) tk₂ := hk₂
  have hy₅' := hk₂'.size_le
  have hsz₄ : (encode ((S.prog, encode (C G, Sampler.Query.marginal .alice 7 z')),
      (S.prog, z')) : Data).size = (esize S.prog +
        (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size + 1) +
        (encode (S.prog, z') : Data).size + 1 := rfl
  have hqA : (encode (Sampler.Query.marginal .alice 7 z') : Data).size ≤
      (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size := by
    show _ ≤ (Data.cons (encode (C G)) (encode (Sampler.Query.marginal .alice 7 z'))).size
    simp only [Data.size_cons]; omega
  have hsim₂ : tA' ≤ dimB G Λ₀ R m * (T2B G U Λ₀ R m + 1) ^ G.deg :=
    htA'.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hex : esize (qOf G Λ₀ R .alice z r) ≤ 4 * dimB G Λ₀ R m + 1 := by
    have := esize_bitStr_le (qOf G Λ₀ R .alice z r)
    have : (qOf G Λ₀ R .alice z r).length = d := length_toBits _
    omega
  have hexe : (encode (qOf G Λ₀ R .alice z r) : Data).size =
    esize (qOf G Λ₀ R .alice z r) := rfl
  have hq₂ : (Data.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .alice 7 z'))).size
    = esize S.prog + (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size + 1 := rfl
  have hR2 : tk₂ ≤ R2B G U Λ₀ R m := by
    have hu := htu₂.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (encode (C G, Sampler.Query.marginal .alice 7 z') : Data).size + tA'
        ≤ 2 * T2B G U Λ₀ R m + dimB G Λ₀ R m * (T2B G U Λ₀ R m + 1) ^ G.deg by omega))
    have : (encode (qOf G Λ₀ R .alice z r) : Data).size = esize (qOf G Λ₀ R .alice z r) := rfl
    unfold R2B; omega
  have hy₅ := hk₂.size_le
  -- stage 3
  obtain ⟨t₃, ht₃, h₃⟩ := (A3 G).computes ((S.prog, z'), qOf G Λ₀ R .alice z r)
  rw [A3_apply] at h₃
  have hT3 : t₃ ≤ T3B G U Λ₀ R m := by
    refine ht₃.trans (polynomial_eval_mono _ ?_)
    have : esize ((S.prog, z'), qOf G Λ₀ R .alice z r) =
      (encode ((S.prog, z'), qOf G Λ₀ R .alice z r) : Data).size := rfl
    rw [this]; omega
  have hy₆ := h₃.size_le
  -- Bob's marginal
  obtain ⟨tB, hB⟩ := S.runs_marginal (C G) .bob 7 z' (by norm_num) le_rfl hz'l
  rw [CLFun.truncate_self] at hB
  obtain ⟨tB', htB', hB'⟩ := sampler_run_bounded S hbS _ hB
  obtain ⟨tu₃, htu₃, hu₃⟩ := U.time_le S.prog _ _ tB' hB'
  have hu₃' : U.univ.Runs (.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .bob 7 z')))
    (encode (qOf G Λ₀ R .bob z r)) tu₃ := hu₃
  obtain ⟨tk₃, htk₃, hk₃⟩ :=
    runUK_runs U.closed (B := encode (qOf G Λ₀ R .alice z r)) hu₃'
  have hk₃' : (runUK U.univ).Runs
      (encode ((S.prog, encode (C G, Sampler.Query.marginal .bob 7 z')),
        qOf G Λ₀ R .alice z r))
      (encode (qOf G Λ₀ R .alice z r, qOf G Λ₀ R .bob z r)) tk₃ := hk₃
  have hsz₆ : (encode ((S.prog, encode (C G, Sampler.Query.marginal .bob 7 z')),
      qOf G Λ₀ R .alice z r) : Data).size = (esize S.prog +
        (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size + 1) +
        esize (qOf G Λ₀ R .alice z r) + 1 := rfl
  have hqB : (encode (Sampler.Query.marginal .bob 7 z') : Data).size ≤
      (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size := by
    show _ ≤ (Data.cons (encode (C G)) (encode (Sampler.Query.marginal .bob 7 z'))).size
    simp only [Data.size_cons]; omega
  have hsim₃ : tB' ≤ dimB G Λ₀ R m * (T3B G U Λ₀ R m + 1) ^ G.deg :=
    htB'.trans (Nat.mul_le_mul hdimB (Nat.pow_le_pow_left (by omega) _))
  have hey : esize (qOf G Λ₀ R .bob z r) ≤ 4 * dimB G Λ₀ R m + 1 := by
    have := esize_bitStr_le (qOf G Λ₀ R .bob z r)
    have : (qOf G Λ₀ R .bob z r).length = d := length_toBits _
    omega
  have heye : (encode (qOf G Λ₀ R .bob z r) : Data).size = esize (qOf G Λ₀ R .bob z r) := rfl
  have hq₃ : (Data.cons (encode S.prog) (encode (C G, Sampler.Query.marginal .bob 7 z'))).size
    = esize S.prog + (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size + 1 := rfl
  have hR3 : tk₃ ≤ R3B G U Λ₀ R m := by
    have hu := htu₃.trans (polynomial_eval_mono U.bound
      (show esize S.prog + (encode (C G, Sampler.Query.marginal .bob 7 z') : Data).size + tB'
        ≤ 2 * T3B G U Λ₀ R m + dimB G Λ₀ R m * (T3B G U Λ₀ R m + 1) ^ G.deg by omega))
    have : (encode (qOf G Λ₀ R .bob z r) : Data).size = esize (qOf G Λ₀ R .bob z r) := rfl
    unfold R3B; omega
  -- assemble
  have w3 := runUK_wellScoped U.closed
  have w23 := seq_wellScoped (A3 G).closed w3
  have wk2 := seq_wellScoped (runUK_wellScoped U.closed) w23
  have wc2 := seq_wellScoped (A2 G).closed wk2
  have wun := seq_wellScoped unaryStage_wellScoped wc2
  have wk1 := seq_wellScoped (runUK_wellScoped U.closed) wun
  have hrun := seq_runs wk1 h₁ (seq_runs wun hk₁' (seq_runs wc2 hn' (seq_runs wk2 h₂
    (seq_runs w23 hk₂' (seq_runs w3 h₃ hk₃')))))
  refine ⟨_, ?_, hrun⟩
  unfold sampB
  omega
end MIPRE.Halting
