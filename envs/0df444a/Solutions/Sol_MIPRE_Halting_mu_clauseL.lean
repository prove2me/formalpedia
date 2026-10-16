-- Prove2me | solution 1 for MIPRE.Halting.mu_clauseL
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:56:08.874975+00:00
-- url     : https://prove2.me/submissions/a452aa0f-9964-435b-a9cd-0cca3476b93e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/TabulateL.lean (solution of MIPRE.Halting.mu_clauseL);
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
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Theorems.Thm_MIPRE_Verifier_length_filter_bitStrsOfLen
import Theorems.Thm_MIPRE_Verifier_sum_filter_length

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Sampler
open Cost
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (S : CL.Sampler ℓ)
/-- **The marginal at the top level is the CL function itself** (`CLFun.truncate_self`), so one
budgeted `marginal` query at level `ℓ` computes `L^w(z)` — which is what the question weights
of the tabulated game are counted from. -/
theorem queryUnder_marginal {n T k : ℕ} (hb : S.TimeBoundAt n T k) (hl : 1 ≤ ℓ) (w : Player)
    (z : BitStr) (hz : z.length = S.dim n) :
    S.queryUnder T k n (Query.marginal w ℓ z)
      = some (encode (toBits ((S.cl n w).eval (ofBits (S.dim n) z)))) := by
  obtain ⟨t, h⟩ := S.runs_marginal n w ℓ z hl le_rfl hz
  rw [CLFun.truncate_self] at h
  exact S.queryUnder_eq hb h
end MIPRE.CL.Sampler

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
theorem questionWeight_weightList (nX nA s : ℕ) (fA fB : BitStr → ℕ)
    (acc : List (ℕ × ℕ × ℕ × ℕ)) (i j : ℕ) :
    (GameData.mk nX nA (weightList s fA fB) acc).questionWeight i j =
      ((Data.bitStrsOfLen s).filter fun z => decide (fA z = i ∧ fB z = j)).length := by
  show ((((weightList s fA fB).filter fun t => decide (t.1 = i ∧ t.2.1 = j)).map
    fun t => t.2.2).sum) = _
  rw [weightList, List.filter_map, List.map_map]
  simp [Function.comp_def]
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
/-- The total weight of the list is `2 ^ s`: every point of `𝔽₂^s` contributes `1`, and the
index pairs it can land on are all in range. That denominator is exactly the one `CL.clDist`
divides by. -/
theorem totalWeight_weightList (nX nA s : ℕ) (fA fB : BitStr → ℕ)
    (acc : List (ℕ × ℕ × ℕ × ℕ))
    (hA : ∀ z ∈ Data.bitStrsOfLen s, fA z < nX + 1)
    (hB : ∀ z ∈ Data.bitStrsOfLen s, fB z < nX + 1) :
    (GameData.mk nX nA (weightList s fA fB) acc).totalWeight = 2 ^ s := by
  show ∑ x : Fin (nX + 1), ∑ y : Fin (nX + 1),
    (GameData.mk nX nA (weightList s fA fB) acc).questionWeight x.val y.val = _
  simp only [questionWeight_weightList]
  rw [sum_filter_length fA fB _ hA hB, Data.length_bitStrsOfLen]
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
theorem bitsToIdx_cons_toBits_eq_iff {s : ℕ} (b c : Bool) (v w : Fin s → CL.𝔽₂) :
    bitsToIdx (b :: CL.toBits v) = bitsToIdx (c :: CL.toBits w) ↔ b = c ∧ v = w :=
  ⟨bitsToIdx_cons_toBits_inj, fun h => by rw [h.1, h.2]⟩
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
/-- **The tabulated marginal is the sampler's, at every string and every level.**  The only
remaining hypothesis is the length condition on the point, which is not a boundedness one. -/
theorem margOf_eq (x : BitStr) (n : ℕ) (w : Player) (z : BitStr)
    (hz : z.length = (Vof G U x).sampler.dim n) :
    margOf (sampData G x) (ansBound G x n) G.deg n w z
      = CL.toBits (((Vof G U x).sampler.cl n w).eval
          (CL.ofBits ((Vof G U x).sampler.dim n) z)) := by
  have hS := sampler_timeBound G x n
  rw [margOf, sampData_eq,
    show Machine.runForD (encode ((G.sampler (descLam x)).prog))
        (encode (n, CL.Sampler.Query.marginal w 7 z))
        (ansBound G x n * ((encode (CL.Sampler.Query.marginal w 7 z) : Data).size + 1) ^ G.deg)
      = (G.sampler (descLam x)).queryUnder (ansBound G x n) G.deg n
          (CL.Sampler.Query.marginal w 7 z) from rfl,
    (G.sampler (descLam x)).queryUnder_marginal hS (by norm_num) w z hz]
  simp [SizedEncoding.decode_encode]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem eXofL_apply (x : BitStr) (n : ℕ) (i : Fin ((tabL G U x n).nX + 1)) :
    Verifier.bitsToIdx ((eXofL G U x n i).1 :: CL.toBits (eXofL G U x n i).2) = (i : ℕ) := by
  rw [eXofL, Equiv.trans_apply, Verifier.bitsToIdx_tagEquiv_symm]
  simp
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem margL_idx_eq (x : BitStr) (n : ℕ) (w : Player)
    (tg : Bool) (z : BitStr) (hz : z.length = (Vof G U x).sampler.dim n)
    (i : Fin ((tabL G U x n).nX + 1)) :
    Verifier.bitsToIdx (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z) = (i : ℕ)
      ↔ (tg = (eXofL G U x n i).1 ∧
          ((Vof G U x).sampler.cl n w).eval (CL.ofBits ((Vof G U x).sampler.dim n) z)
            = (eXofL G U x n i).2) := by
  rw [margOf_eq G U x n w z hz, ← eXofL_apply G U x n i,
    Verifier.bitsToIdx_cons_toBits_eq_iff]
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
theorem _root_.solution (x : BitStr) (n : ℕ)
    (i j : Fin ((tabL G U x n).nX + 1)) :
    (tabL G U x n).game.μ i j
      = ((Vof G U x).doubledGame n (ansBound G x n)).μ
          (eXofL G U x n i) (eXofL G U x n j) := by
  classical
  have hdim : dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n :=
    dimOf_eq G U x n
  have hlen : ∀ (w : Player) (z : BitStr), z.length = (Vof G U x).sampler.dim n →
      (margOf (sampData G x) (ansBound G x n) G.deg n w z).length
        = (Vof G U x).sampler.dim n := by
    intro w z hz
    rw [margOf_eq G U x n w z hz, CL.length_toBits]
  have hmem : ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n),
      z.length = (Vof G U x).sampler.dim n := by
    intro z hz
    rw [← hdim]; exact (Data.mem_bitStrsOfLen _ _).1 hz
  have hrange : ∀ (tg : Bool) (w : Player),
      ∀ z ∈ Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n),
        Verifier.bitsToIdx (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z)
          < (tabL G U x n).nX + 1 := by
    intro tg w z hz
    have hlt := Verifier.bitsToIdx_lt (tg :: margOf (sampData G x) (ansBound G x n) G.deg n w z)
    rw [List.length_cons, hlen w z (hmem z hz)] at hlt
    rw [tabL_nX G U x n]
    exact hlt
  have htot : (tabL G U x n).totalWeight = 2 ^ dimOf (sampData G x) (ansBound G x n) G.deg n :=
    Verifier.totalWeight_weightList _ _ _ _ _ _ (hrange false .alice) (hrange true .bob)
  have hqw : ∀ a b : ℕ, (tabL G U x n).questionWeight a b
      = ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter fun z =>
          decide (Verifier.bitsToIdx
              (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = a
            ∧ Verifier.bitsToIdx
              (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = b)).length :=
    fun a b => Verifier.questionWeight_weightList _ _ _ _ _ _ a b
  rw [GameData.game_μ, htot, if_neg (Nat.two_pow_pos _).ne', hqw,
    show ((Vof G U x).doubledGame n (ansBound G x n)).μ
        (eXofL G U x n i) (eXofL G U x n j)
      = if (eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true then
          (Vof G U x).sampler.dist n (eXofL G U x n i).2 (eXofL G U x n j).2 else 0 from rfl]
  by_cases htag : (eXofL G U x n i).1 = false ∧ (eXofL G U x n j).1 = true
  · rw [if_pos htag]
    have hnum : ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter
          fun z => decide (Verifier.bitsToIdx
              (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
            ∧ Verifier.bitsToIdx
              (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ))).length
        = (Finset.univ.filter fun v : (Vof G U x).Questions n =>
            ((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2).card := by
      rw [hdim]
      rw [show ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
          decide (Verifier.bitsToIdx
              (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
            ∧ Verifier.bitsToIdx
              (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ)))
          = ((Data.bitStrsOfLen ((Vof G U x).sampler.dim n)).filter fun z =>
            (fun v : (Vof G U x).Questions n =>
              decide (((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
                ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2))
              (CL.ofBits ((Vof G U x).sampler.dim n) z)) from ?_]
      · rw [Verifier.length_filter_bitStrsOfLen (s := (Vof G U x).sampler.dim n)
          (fun v => decide (((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
            ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2))]
        congr 1
        ext v
        simp
      · refine List.filter_congr fun z hz => ?_
        have hz' : z.length = (Vof G U x).sampler.dim n :=
          (Data.mem_bitStrsOfLen _ _).1 hz
        simp only [decide_eq_decide]
        rw [margL_idx_eq G U x n .alice false z hz' i,
          margL_idx_eq G U x n .bob true z hz' j, htag.1, htag.2]
        simp
    rw [hnum,
      show (Vof G U x).sampler.dist n (eXofL G U x n i).2 (eXofL G U x n j).2
        = ((Finset.univ.filter fun v : (Vof G U x).Questions n =>
            ((Vof G U x).sampler.cl n .alice).eval v = (eXofL G U x n i).2
              ∧ ((Vof G U x).sampler.cl n .bob).eval v = (eXofL G U x n j).2).card : ℝ)
          / (Fintype.card ((Vof G U x).Questions n) : ℝ) from rfl]
    congr 1
    rw [hdim]
    simp [Verifier.Questions]
  · rw [if_neg htag]
    have hnil : ((Data.bitStrsOfLen (dimOf (sampData G x) (ansBound G x n) G.deg n)).filter
        fun z => decide (Verifier.bitsToIdx
            (false :: margOf (sampData G x) (ansBound G x n) G.deg n .alice z) = (i : ℕ)
          ∧ Verifier.bitsToIdx
            (true :: margOf (sampData G x) (ansBound G x n) G.deg n .bob z) = (j : ℕ))) = [] := by
      refine List.filter_eq_nil_iff.2 fun z hz => ?_
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      exact htag ⟨((margL_idx_eq G U x n .alice false z (hmem z hz) i).1 h1).1.symm,
        ((margL_idx_eq G U x n .bob true z (hmem z hz) j).1 h2).1.symm⟩
    rw [hnil]
    simp
end MIPRE.Halting
