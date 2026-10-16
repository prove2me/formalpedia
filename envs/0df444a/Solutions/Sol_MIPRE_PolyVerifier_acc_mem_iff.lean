-- Prove2me | solution 1 for MIPRE.PolyVerifier.acc_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:52:34.088404+00:00
-- url     : https://prove2.me/submissions/ccfd139c-290b-496a-b1c8-3bcbdf8b3572

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ClassMIPStarTab.lean (solution of MIPRE.PolyVerifier.acc_mem_iff);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Machine_runs_of_runForD
import Theorems.Thm_MIPRE_Verifier_answerEquiv_symm_val

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Machine
/-- **The decision procedure.** For a program that halts within the budget, whether it returns
a given value is decidable. -/
theorem runForD_eq_some_iff {p : Prog} {x r : Data} {k : ℕ}
    (hb : HaltsWithin p x k) : runForD (encode p) x k = some r ↔ ∃ t, p.Runs x r t := by
  obtain ⟨r₀, t₀, ht₀, h₀⟩ := hb
  refine ⟨runs_of_runForD, fun ⟨t, h⟩ => ?_⟩
  obtain ⟨rfl, -⟩ := h₀.deterministic h
  exact runForD_eq_some h₀ ht₀
end MIPRE.Cost.Machine

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
theorem mem_accListLE_iff {T : ℕ} {fA fB : BitStr → ℕ}
    {acc? : BitStr → BitStr → BitStr → BitStr → Bool} {i j k l : ℕ} :
    (i, j, k, l) ∈ accListLE T fA fB acc? ↔
      ∃ x ∈ Data.bitStrsLE T, ∃ y ∈ Data.bitStrsLE T,
        ∃ a ∈ Data.bitStrsLE T, ∃ b ∈ Data.bitStrsLE T,
          acc? x y a b = true ∧ i = fA x ∧ j = fB y ∧
            k = (Data.bitStrsLE T).idxOf a ∧ l = (Data.bitStrsLE T).idxOf b := by
  simp only [accListLE, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, h⟩
    by_cases hc : acc? x y a b
    · rw [if_pos hc] at h
      obtain ⟨hi, hj, hk, hl⟩ : fA x = i ∧ fB y = j ∧
          (Data.bitStrsLE T).idxOf a = k ∧ (Data.bitStrsLE T).idxOf b = l := by simpa using h
      exact ⟨x, hx, y, hy, a, ha, b, hb, hc, hi.symm, hj.symm, hk.symm, hl.symm⟩
    · rw [if_neg hc] at h; exact absurd h (by simp)
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, hc, rfl, rfl, rfl, rfl⟩
    exact ⟨x, hx, y, hy, a, ha, b, hb, by rw [if_pos hc]⟩
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
theorem eA_apply (z : BitStr) (k : Fin ((V.tab z).nA + 1)) :
    (Data.bitStrsLE (V.B z)).idxOf (V.eA z k).1 = (k : ℕ) := by
  rw [eA, Equiv.trans_apply, aEquiv_apply]
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
/-- **The budgeted verdict is acceptance**, on an efficient input. -/
theorem accC_eq {z : BitStr} (h : V.Efficient z) (x y a b : BitStr) :
    accC (encode V.decider) V.bound z x y a b = true ↔ V.Accepts z x y a b := by
  rw [accC, decide_eq_true_iff, Machine.runForD_eq_some_iff (h.decider_time x y a b)]
  rfl
end MIPRE.PolyVerifier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem _root_.solution {z : BitStr} (h : V.Efficient z) (i j : Fin ((V.tab z).nX + 1))
    (k l : Fin ((V.tab z).nA + 1)) :
    ((i : ℕ), (j : ℕ), (k : ℕ), (l : ℕ)) ∈ (V.tab z).acc
      ↔ ((V.eX z i).1 = false ∧ (V.eX z j).1 = true ∧
          V.Accepts z (V.eX z i).2.1 (V.eX z j).2.1 (V.eA z k).1 (V.eA z l).1) := by
  have hqmem : ∀ m : Fin ((V.tab z).nX + 1), (V.eX z m).2.1 ∈ Data.bitStrsLE (V.B z) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (V.eX z m).2.2
  have hamem : ∀ m : Fin ((V.tab z).nA + 1), (V.eA z m).1 ∈ Data.bitStrsLE (V.B z) :=
    fun m => (Data.mem_bitStrsLE _ _).2 (V.eA z m).2
  rw [show (V.tab z).acc = accListLE (V.B z) (qIdx (V.B z) false) (qIdx (V.B z) true)
      (accC (encode V.decider) V.bound z) from rfl, mem_accListLE_iff]
  constructor
  · rintro ⟨x, hx, y, hy, a, ha, b, hb, hacc, hi, hj, hk, hl⟩
    obtain ⟨hti, hxi⟩ := (V.qIdx_eq_iff' z false hx i).1 hi.symm
    obtain ⟨htj, hyj⟩ := (V.qIdx_eq_iff' z true hy j).1 hj.symm
    have ha' : a = (V.eA z k).1 := (List.idxOf_inj ha).1 (by rw [← hk, V.eA_apply])
    have hb' : b = (V.eA z l).1 := (List.idxOf_inj hb).1 (by rw [← hl, V.eA_apply])
    refine ⟨hti.symm, htj.symm, ?_⟩
    rw [← hxi, ← hyj, ← ha', ← hb']
    exact (V.accC_eq h x y a b).1 hacc
  · rintro ⟨ht1, ht2, hacc⟩
    refine ⟨_, hqmem i, _, hqmem j, _, hamem k, _, hamem l, (V.accC_eq h _ _ _ _).2 hacc,
      ?_, ?_, (V.eA_apply z k).symm, (V.eA_apply z l).symm⟩
    · rw [← ht1, V.eX_apply z i]
    · rw [← ht2, V.eX_apply z j]
end MIPRE.PolyVerifier
