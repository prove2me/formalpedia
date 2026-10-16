-- Prove2me | solution 1 for MIPRE.PolyVerifier.mu_clause
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:51:08.985346+00:00
-- url     : https://prove2.me/submissions/853e33b9-93e9-43d8-95fd-f61f41c23a5f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ClassMIPStarTab.lean (solution of MIPRE.PolyVerifier.mu_clause);
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab
import Theorems.Thm_MIPRE_PolyVerifier_sampleC_eq
import Theorems.Thm_MIPRE_Verifier_answerEquiv_symm_val
import Theorems.Thm_MIPRE_Verifier_sum_filter_length

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
variable (V : PolyVerifier)
theorem game_μ (z : BitStr) (x y : Answers (V.B z)) :
    (V.game z).μ x y = (V.seedCount z x y : ℝ) / 2 ^ V.B z := rfl
end MIPRE.PolyVerifier

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

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem aEquiv_apply (T : ℕ) (k : Fin (N T)) :
    (Data.bitStrsLE T).idxOf (aEquiv T k).1 = (k : ℕ) := by
  rw [← answerEquiv_symm_val, aEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem finTwoEquiv_ite (a : Fin 2) : (if finTwoEquiv a then 1 else 0) = (a : ℕ) := by
  fin_cases a <;> rfl
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem qEquiv_apply (T : ℕ) (i : Fin (2 * N T)) :
    qIdx T (qEquiv T i).1 (qEquiv T i).2.1 = (i : ℕ) := by
  obtain ⟨⟨a, b⟩, h⟩ : ∃ p : Fin 2 × Fin (N T), finProdFinEquiv.symm i = p :=
    ⟨_, rfl⟩
  have hi : i = finProdFinEquiv (a, b) := by rw [← h, Equiv.apply_symm_apply]
  have h1 : (qEquiv T i).1 = finTwoEquiv a := by
    simp only [qEquiv, Equiv.trans_apply, h, Equiv.prodCongr_apply, Prod.map_fst]
  have h2 : (qEquiv T i).2 = aEquiv T b := by
    simp only [qEquiv, aEquiv, Equiv.trans_apply, h, Equiv.prodCongr_apply, Prod.map_snd]
  rw [qIdx, h1, h2, aEquiv_apply, finTwoEquiv_ite, hi]
  rfl
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem qIdx_lt (T : ℕ) (tg : Bool) {x : BitStr} (hx : x ∈ Data.bitStrsLE T) :
    qIdx T tg x < 2 * N T := by
  have := List.idxOf_lt_length_iff.2 hx
  unfold qIdx N
  cases tg <;> simp <;> omega
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem qIdx_inj (T : ℕ) {tg tg' : Bool} {x x' : BitStr} (hx : x ∈ Data.bitStrsLE T)
    (hx' : x' ∈ Data.bitStrsLE T) (h : qIdx T tg x = qIdx T tg' x') : tg = tg' ∧ x = x' := by
  have h1 := List.idxOf_lt_length_iff.2 hx
  have h2 := List.idxOf_lt_length_iff.2 hx'
  unfold qIdx N at h
  have htg : tg = tg' := by
    cases tg <;> cases tg' <;> simp at h ⊢ <;> omega
  subst htg
  refine ⟨rfl, (List.idxOf_inj hx).1 ?_⟩
  cases tg <;> simp at h <;> omega
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem eX_apply (z : BitStr) (i : Fin ((V.tab z).nX + 1)) :
    qIdx (V.B z) (V.eX z i).1 (V.eX z i).2.1 = (i : ℕ) := by
  rw [eX, Equiv.trans_apply, qEquiv_apply]
  rfl
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem qIdx_eq_iff' (z : BitStr) (tg : Bool) {x : BitStr} (hx : x ∈ Data.bitStrsLE (V.B z))
    (i : Fin ((V.tab z).nX + 1)) :
    qIdx (V.B z) tg x = (i : ℕ) ↔ tg = (V.eX z i).1 ∧ x = (V.eX z i).2.1 := by
  constructor
  · intro h
    exact qIdx_inj _ hx ((Data.mem_bitStrsLE _ _).2 (V.eX z i).2.2)
      (h.trans (V.eX_apply z i).symm)
  · rintro ⟨rfl, rfl⟩
    exact V.eX_apply z i
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem sampleC_fst_mem {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r ∈ Data.bitStrsOfLen (V.B z)) :
    (sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r).1 ∈
      Data.bitStrsLE (V.B z) := by
  rw [V.sampleC_eq h ((Data.mem_bitStrsOfLen _ _).1 hr)]
  exact (Data.mem_bitStrsLE _ _).2 (V.questions z r).1.2
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem sampleC_snd_mem {z : BitStr} (h : V.Efficient z) {r : BitStr}
    (hr : r ∈ Data.bitStrsOfLen (V.B z)) :
    (sampleC (encode V.sampler) (V.bound.eval (z.length + V.B z)) z r).2 ∈
      Data.bitStrsLE (V.B z) := by
  rw [V.sampleC_eq h ((Data.mem_bitStrsOfLen _ _).1 hr)]
  exact (Data.mem_bitStrsLE _ _).2 (V.questions z r).2.2
end MIPRE.PolyVerifier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem _root_.solution {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1)) :
    (V.tab z).game.μ i j = (V.game z).doubled.μ (V.eX z i) (V.eX z j) := by
  classical
  set T := V.B z with hT
  have hrange : ∀ (tg : Bool) (f : BitStr × BitStr → BitStr),
      (∀ r ∈ Data.bitStrsOfLen T,
        f (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r) ∈ Data.bitStrsLE T) →
      ∀ r ∈ Data.bitStrsOfLen T,
        qIdx T tg (f (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r)) <
          (V.tab z).nX + 1 := by
    intro tg f hf r hr
    rw [V.tab_nX z]
    exact qIdx_lt T tg (hf r hr)
  have htot : (V.tab z).totalWeight = 2 ^ T :=
    totalWeight_weightList _ _ _ _ _ _
      (hrange false Prod.fst fun r hr => V.sampleC_fst_mem h hr)
      (hrange true Prod.snd fun r hr => V.sampleC_snd_mem h hr)
  have hqw : ∀ a b : ℕ, (V.tab z).questionWeight a b
      = ((Data.bitStrsOfLen T).filter fun r =>
          decide (qIdx T false (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).1 = a
            ∧ qIdx T true (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).2
              = b)).length :=
    fun a b => questionWeight_weightList _ _ _ _ _ _ a b
  rw [GameData.game_μ, htot, if_neg (Nat.two_pow_pos _).ne', hqw,
    show (V.game z).doubled.μ (V.eX z i) (V.eX z j)
      = if (V.eX z i).1 = false ∧ (V.eX z j).1 = true then
          (V.game z).μ (V.eX z i).2 (V.eX z j).2 else 0 from rfl]
  by_cases htag : (V.eX z i).1 = false ∧ (V.eX z j).1 = true
  · rw [if_pos htag, V.game_μ, seedCount]
    push_cast
    congr 2
    apply congrArg List.length
    refine List.filter_congr fun r hr => ?_
    have hr' : r.length = T := (Data.mem_bitStrsOfLen _ _).1 hr
    rw [V.sampleC_eq h hr']
    simp only [decide_eq_decide]
    rw [V.qIdx_eq_iff' z false ((Data.mem_bitStrsLE _ _).2 (V.questions z r).1.2) i,
      V.qIdx_eq_iff' z true ((Data.mem_bitStrsLE _ _).2 (V.questions z r).2.2) j,
      ← htag.1, ← htag.2]
    simp only [true_and]
    rw [Prod.ext_iff]
    exact and_congr Subtype.ext_iff.symm Subtype.ext_iff.symm
  · rw [if_neg htag]
    have hnil : ((Data.bitStrsOfLen T).filter fun r =>
        decide (qIdx T false (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).1
            = (i : ℕ)
          ∧ qIdx T true (sampleC (encode V.sampler) (V.bound.eval (z.length + T)) z r).2
            = (j : ℕ))) = [] := by
      refine List.filter_eq_nil_iff.2 fun r hr => ?_
      simp only [decide_eq_true_eq, not_and]
      intro h1 h2
      exact htag ⟨((V.qIdx_eq_iff' z false (V.sampleC_fst_mem h hr) i).1 h1).1.symm,
        ((V.qIdx_eq_iff' z true (V.sampleC_snd_mem h hr) j).1 h2).1.symm⟩
    rw [hnil]
    simp
end MIPRE.PolyVerifier
