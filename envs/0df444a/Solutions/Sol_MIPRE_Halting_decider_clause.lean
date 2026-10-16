-- Prove2me | solution 1 for MIPRE.Halting.decider_clause
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:28:00.485229+00:00
-- url     : https://prove2.me/submissions/7f4bc90e-a95d-4bc7-8c12-6507316e967d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/CompressorCost.lean (solution of MIPRE.Halting.decider_clause);
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
import Theorems.Thm_MIPRE_Halting_outDec_cost
import Theorems.Thm_MIPRE_Halting_wrapCoreCost_le_decZ

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_lamOf : PolyBounded lamOf :=
  (PolyBounded.two_pow_size 0 2).mono fun n => by simp [lamOf]
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
/-- **The output's decider, on every input.** -/
theorem outDec_wrap_cost {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (m : ℕ)
    (d : Data) :
    ∃ r t, t ≤ wrapCoreCost U (G.sampler (lamOf n)) (outDec G U c n (lamOf n))
        (fun m => G.bound.eval (m + lamOf n)) G.deg m
        (innerBound G U (esize c) n x.length (lamOf n) (esize (lamOf n)) m d.size) d.size ∧
      (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n)))).Runs
        (.cons (encode m) d) r t :=
  wrapCore_cost' U (G.sampler (lamOf n)) (outDec G U c n (lamOf n)) _ G.deg
    (fun m d => G.sampler_time (lamOf n) m d) m _
    (fun d => outDec_cost G U hsd (lamOf n) m d) d
end MIPRE.Halting

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_readIter : PolyBounded fun z => readIter U z z (z + 1) := by
  have hz := PolyBounded.id
  have hL : PolyBounded fun z : ℕ => z + 1 := hz.add_const 1
  have hsz : PolyBounded fun z : ℕ => Nat.size (z + 1) := PolyBounded.size.comp hL
  unfold readIter
  exact (((((PolyBounded.eval _ ((hz.add ((hsz.const_mul 4).add_const 1)).add
    ((hz.add_const 1).mul ((hsz.add_const 1).pow 2)))).add (hz.const_mul 3)).add
    (((hsz.const_mul 4).add_const 1).const_mul 4)).add ((hL.const_mul 4).add_const 1)).add
    ((((hsz.add_const 2).mul (((((hsz.const_mul 4).add_const 1).const_mul 8).add
      (hsz.const_mul 8)).add_const 60))).const_mul 2)).add_const 30
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_sampBound : PolyBounded fun z => sampBound G (z + 1) :=
  PolyBounded.eval _ (PolyBounded.id.add_const 1 |>.add_const 1)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_wBound : PolyBounded fun z => wBound G U (z + 1) := by
  unfold wBound
  exact (((polyBounded_sampBound G).add (PolyBounded.id.add_const 1 |>.add_const 1)).add_const
    (2 * esize U.univ)).add_const wrapNodes
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_kBound : PolyBounded kBound :=
  (PolyBounded.size.const_mul 4).add_const 5
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_fBound : PolyBounded fun z => fBound G U (z + 1) z := by
  unfold fBound
  exact ((((polyBounded_sampBound G).add polyBounded_kBound).add_const 53).add
    ((((polyBounded_wBound G U).add polyBounded_kBound).add_const 53)))
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
/-- The size of `λ(z)`'s encoding, as the bound `8 · size z + 5`. -/
theorem polyBounded_lsize : PolyBounded fun z => 8 * Nat.size z + 5 :=
  (PolyBounded.size.const_mul 8).add_const 5
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_prepBound :
    PolyBounded fun z => prepBound G U z z (z + 1) (8 * Nat.size z + 5) := by
  have hz := PolyBounded.id
  have hL : PolyBounded fun z : ℕ => z + 1 := hz.add_const 1
  unfold prepBound
  refine ((((((((((hL.mul ((polyBounded_readIter U).add_const 1)).add
    ((hz.add_const 2).mul ((hz.const_mul 4).add_const 14))).add hz).add_const 7).add
    ((hz.add_const 2).mul ((((hz.const_mul 4).add_const 1).add (hz.const_mul 2)).add_const 25))).add
    ((hz.const_mul 4).add_const 1)).add
    (((hz.add_const 3).mul (hz.add_const 26)).add ((hL.const_mul 3).add_const 10))).add
    ((((polyBounded_sampBound G).add (polyBounded_wBound G U)).add (polyBounded_fBound G U)).add
      (PolyBounded.eval _ (((polyBounded_fBound G U).add polyBounded_lsize).add_const 2)))).add
    ((((((hz.const_mul 2).add (((hz.const_mul 4).add_const 1).const_mul 4)).add
      (hL.const_mul 12)).add ((polyBounded_sampBound G).const_mul 2)).add
      ((polyBounded_wBound G U).const_mul 3)).add (polyBounded_kBound.const_mul 6))).add
    ((((polyBounded_fBound G U).const_mul 2).add (polyBounded_lsize.const_mul 2)).add_const 200)).add
    ((hz.const_mul 22).add ((polyBounded_readIter U).add_const 136)) |>.mono
    fun z => by ring_nf; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_innerBound :
    PolyBounded fun z => innerBound G U z z (z + 1) (lamOf z) (8 * Nat.size z + 5) z z := by
  have hz := PolyBounded.id
  have hsz := PolyBounded.size
  have hm : PolyBounded fun z : ℕ => 4 * Nat.size z + 1 + z + 1 :=
    (((hsz.const_mul 4).add_const 1).add hz).add_const 1
  unfold innerBound
  exact (((((polyBounded_prepBound G U).const_mul 3).add
    ((((hz.add ((hsz.const_mul 4).add_const 1)).add polyBounded_lsize).add_const 2).const_mul 2)).add
    (hm.const_mul 3)).add
    (PolyBounded.eval _ (((PolyBounded.eval _ (((polyBounded_fBound G U).add
      polyBounded_lsize).add_const 2)).add hm).add
      ((PolyBounded.eval _ (hz.add polyBounded_lamOf)).mul ((hz.add_const 1).pow G.deg))))).add_const 15
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_sigZ : PolyBounded (sigZ G) :=
  PolyBounded.eval _ ((PolyBounded.size.const_mul 8).add_const 5)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_deltaZ : PolyBounded (deltaZ G U) :=
  ((((PolyBounded.const _).add PolyBounded.id).add ((PolyBounded.size.const_mul 4).add_const 1)).add
    ((PolyBounded.size.const_mul 8).add_const 5)).add_const 37
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_iotaZ : PolyBounded (iotaZ G U) := polyBounded_innerBound G U
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_headZ : PolyBounded (headZ G U) := by
  have hσ := polyBounded_sigZ G
  have hβ := polyBounded_sampZ G
  have hs : PolyBounded fun z : ℕ => 4 * Nat.size z + 1 := (PolyBounded.size.const_mul 4).add_const 1
  unfold headZ
  exact (((((((hσ.add hs).add (PolyBounded.const _)).add ((hβ.const_mul 4).add_const 1)).add
    (hβ.mul (PolyBounded.const _))).add
    (PolyBounded.eval _ ((hσ.add ((hs.add_const _).add_const 1)).add (hβ.mul (PolyBounded.const _))))).add
    ((hβ.add_const 2).mul ((((hβ.add_const 1).mul ((hβ.const_mul 4).add_const 14)).add
      (((hβ.const_mul 4).add_const 1).const_mul 7)).add ((hβ.const_mul 8).add_const 90)))).add_const 10)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem polyBounded_decZ : PolyBounded (decZ G U) := by
  have hz := PolyBounded.id
  have hs : PolyBounded fun z : ℕ => 4 * Nat.size z + 1 := (PolyBounded.size.const_mul 4).add_const 1
  have hδ := polyBounded_deltaZ G U
  unfold decZ
  exact (((((polyBounded_headZ G U).pow 2).const_mul 60 |>.add_const 4).add
    (((((hz.add (polyBounded_sampZ G)).add_const 30).pow 2).const_mul 60).const_mul 2)).add
    (((((hδ.add hs).add hz).add_const 2).const_mul 2).add
      (PolyBounded.eval _ ((hδ.add ((hs.add hz).add_const 1)).add (polyBounded_iotaZ G U))))).add_const 20
end MIPRE.Halting

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution : ∃ n₀, ∀ n, n₀ ≤ n → ∀ (c : Prog) (x : BitStr), 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 → ∀ m, 2 ≤ m →
    (Vof G U (comprStr G U c n (lamOf n))).decider.TimeBoundAt m (m ^ n) n := by
  obtain ⟨n₀, hn₀⟩ := (polyBounded_decZ G U).absorb
  refine ⟨n₀, fun n hn c x hc hsd hx m hm d => ?_⟩
  rw [Vof_comprStr']
  show HaltsWithin (wrapCore U.univ (G.sampler (lamOf n)).prog (encode (outDec G U c n (lamOf n))))
    (.cons (encode m) d) _
  obtain ⟨r, t, ht, hrun⟩ := outDec_wrap_cost G U hsd m d
  refine ⟨r, t, ht.trans ?_, hrun⟩
  have hz := hn₀ n hn m hm (d.size + 1) (by omega)
  refine le_trans (wrapCoreCost_le_decZ G U (by omega) hx ?_ ?_ ?_) hz
  · nlinarith
  · nlinarith
  · nlinarith
end MIPRE.Halting
