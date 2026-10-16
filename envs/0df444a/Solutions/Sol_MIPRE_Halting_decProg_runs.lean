-- Prove2me | solution 1 for MIPRE.Halting.decProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:19:21.078988+00:00
-- url     : https://prove2.me/submissions/fb5e4884-2a25-478b-86fa-00d6530ab424

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassVerifier.lean (solution of MIPRE.Halting.decProg_runs);
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
import Theorems.Thm_MIPRE_Halting_D1_apply

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem _root_.solution (z x y a b : BitStr) :
    ∃ r t, t ≤ decB G U UT Λ₀ K R (z.length + x.length + y.length + a.length + b.length) ∧
      (decProg G U UT Λ₀ K R).Runs (encode (z, x, y, a, b)) r t := by
  set m := z.length + x.length + y.length + a.length + b.length with hm
  obtain ⟨t₀, ht₀, e₀⟩ := (D1 G U UT Λ₀ K R).computes (z, x, y, a, b)
  rw [D1_apply] at e₀
  have hT : t₀ ≤ TDB G U UT Λ₀ K R m := by
    refine ht₀.trans (polynomial_eval_mono _ ?_)
    have := esize_bitStr_le z; have := esize_bitStr_le x; have := esize_bitStr_le y
    have := esize_bitStr_le a; have := esize_bitStr_le b
    simp only [esize_prod]; omega
  -- the atoms of the wrapped decider's cost
  have hzB1 : esize (R z) ≤ zB G Λ₀ R m := by
    have h1 := R.esize_apply_le z
    have h2 := esize_bitStr_le z
    have h3 := polynomial_eval_mono R.timeBound (show esize z ≤ 4 * m + 1 by omega)
    unfold zB; omega
  have hzB2 : C G ≤ zB G Λ₀ R m := by unfold zB; omega
  have hzB3 : lamz Λ₀ R z ≤ zB G Λ₀ R m := by
    have := lamz_le Λ₀ R z m (by omega)
    unfold zB; omega
  have hzB4 : (encode (x, y, a, b) : Data).size ≤ zB G Λ₀ R m := by
    have := esize_bitStr_le x; have := esize_bitStr_le y
    have := esize_bitStr_le a; have := esize_bitStr_le b
    have e : (encode (x, y, a, b) : Data).size =
      esize x + (esize y + (esize a + esize b + 1) + 1) + 1 := rfl
    unfold zB; omega
  -- the rejecting branch
  have hrej : (D1 G U UT Λ₀ K R).code.Runs (encode (z, x, y, a, b))
      (encode (falseProg, Data.nil)) t₀ → ∃ r t, t ≤ decB G U UT Λ₀ K R m ∧
        (decProg G U UT Λ₀ K R).Runs (encode (z, x, y, a, b)) r t := by
    intro e₁
    have hsz := e₁.size_le
    obtain ⟨tu, htu, hu⟩ := U.time_le falseProg Data.nil (encode false) _
      (Eval.const [Data.nil] (encode false))
    have hu' : U.univ.Runs (encode (falseProg, Data.nil)) (encode false) tu := hu
    refine ⟨encode false, _, ?_, seq_runs U.closed e₁ hu'⟩
    have hsz' : (encode (falseProg, Data.nil) : Data).size = esize falseProg + 1 + 1 := rfl
    have hcc : (encode false : Data).size ≤ constCost := by unfold constCost; omega
    have hu2 := htu.trans (polynomial_eval_mono U.bound
      (show esize falseProg + Data.nil.size + (encode false : Data).size ≤
        TDB G U UT Λ₀ K R m + (WZ G U UT (semL G U) (zB G Λ₀ R m) + constCost) by
          simp only [Data.size_nil]; omega))
    unfold decB; omega
  split_ifs at e₀ with ha hb
  · -- the wrapped decider, through the universal machine
    have hy := e₀.size_le
    obtain ⟨r, tc, htc, hc⟩ := Vhalt_decider_cost G U UT (semL G U) (R z) (lamz Λ₀ R z) (C G)
      (encode (x, y, a, b))
    have hW := htc.trans (wrapCoreCost_le_WZ G U UT (semL G U) (R z) hzB1 hzB2 hzB3 hzB4)
    have hc' : (wdec G U UT Λ₀ R z).Runs (encode (C G, x, y, a, b)) r tc := hc
    obtain ⟨tu, htu, hu⟩ := U.time_le _ _ _ tc hc'
    have hu' : U.univ.Runs (encode (wdec G U UT Λ₀ R z, encode (C G, x, y, a, b))) r tu := hu
    refine ⟨r, _, ?_, seq_runs U.closed e₀ hu'⟩
    have hsz : (encode (wdec G U UT Λ₀ R z, encode (C G, x, y, a, b)) : Data).size =
      esize (wdec G U UT Λ₀ R z) + (encode (C G, x, y, a, b) : Data).size + 1 := rfl
    have hu2 := htu.trans (polynomial_eval_mono U.bound
      (show esize (wdec G U UT Λ₀ R z) + (encode (C G, x, y, a, b) : Data).size + tc ≤
        TDB G U UT Λ₀ K R m + (WZ G U UT (semL G U) (zB G Λ₀ R m) + constCost) by omega))
    unfold decB; omega
  · exact hrej e₀
  · exact hrej e₀
end MIPRE.Halting
