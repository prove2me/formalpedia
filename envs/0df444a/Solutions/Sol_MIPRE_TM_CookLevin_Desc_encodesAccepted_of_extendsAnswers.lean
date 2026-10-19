-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.encodesAccepted_of_extendsAnswers
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:34:43.729993+00:00
-- url     : https://prove2.me/submissions/a744b7d0-5f37-4799-bd7c-680cbd67292c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sat.lean (solution of MIPRE.TM.CookLevin.Desc.encodesAccepted_of_extendsAnswers);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Theorems.Thm_MIPRE_SAT_Fml_exists_circuit
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_chk_isCheckCircuit
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decide_val_inputCellVal
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_ans
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_idxOf_ans
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_sat_tableau_of_sat_formula3
import Theorems.Thm_MIPRE_TM_CookLevin_acceptsIn_of_tableau_sat
import Theorems.Thm_MIPRE_TM_Interp_acceptsWithin_of_accepts

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem WellFormed.refsLt {C : Circuit} (h : C.WellFormed) : C.RefsLt := h.refs_lt
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem WellFormed.inputsLt {C : Circuit} (h : C.WellFormed) : C.InputsLt := h.inputs_lt
end
end MIPRE.SAT.Circuit

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
/-- Boundary cells, numerically. -/
theorem isBdry_iff {S : ℕ} (p : Pos S) : p.IsBdry ↔ (p : ℕ) < 2 ∨ 2 * S + 5 ≤ p := by
  unfold Pos.IsBdry numCells
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_spec : chk.WellFormed ∧ chk.inputs = winCard 7 6 Sym Ctl ∧
    chk.size ≤ 7 * 2 ^ winCard 7 6 Sym Ctl ∧
    ∀ x : Fin (winCard 7 6 Sym Ctl) → Bool, chk.evalBits (List.ofFn x) = chkFun x :=
  (Fml.exists_circuit (winCard 7 6 Sym Ctl) chkFun).choose_spec
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_wellFormed : chk.WellFormed := chk_spec.1
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_refsLt : chk.RefsLt := chk_wellFormed.refsLt
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_inputsLt : chk.InputsLt := chk_wellFormed.inputsLt
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_gates_ne : chk.gates ≠ [] := chk_wellFormed.nonempty
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G T : ℕ)
theorem rOf_lt (j : ℕ) (hj : j < 4 * T) : rOf T j < 2 * T := by
  unfold rOf; split_ifs <;> omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
omit [Fintype Symbol] [Fintype State] [DecidableEq Symbol] [DecidableEq State] in
theorem unit_eval (f : TabVar i w Symbol State S G → Bool) (v : TabVar i w Symbol State S G)
    (b : Bool) : (unit v b).eval f = true ↔ f v = b := by
  cases b <;> cases h : f v <;> simp [unit, cl, Clause3.eval, Lit.eval, h]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem bits_boolsOf (s : List Sym) (h : ∀ c ∈ s, c = Sym.zero ∨ c = Sym.one) :
    bits (boolsOf s) = s := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    rw [boolsOf, List.map_cons, bits_cons, ← boolsOf,
      ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    rcases h c (List.mem_cons_self ..) with rfl | rfl <;> simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (𝒟 : Decider) (n T : ℕ) (x y : BitStr) (e : ℕ)
/-- A blank at an interior cell bounds the string on the tape. -/
theorem length_le_of_inputCellVal_blank {S : ℕ} (s : List Sym) (p : Pos S) (hnb : ¬ Pos.IsBdry p)
    (h3 : 3 ≤ (p : ℕ)) (h : inputCellVal s p = CellVal.blank) : s.length ≤ (p : ℕ) - 3 := by
  rw [inputCellVal, if_neg hnb] at h
  by_contra hlt
  rw [dif_pos ⟨h3, by omega⟩] at h
  exact absurd h (by simp)
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
variable (𝒟 : Decider) (n T : ℕ) (x y : BitStr) (e : ℕ)
theorem _root_.solution (hT : T ≤ Sof e)
    (hlen : FixedLen e 𝒟.prog n T x y) (hTm : T + 3 < 2 ^ W e)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (a b : Fin (2 * T) → Bool)
    (h : ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)) a b) :
    EncodesAccepted 𝒟 n x y T a b := by
  obtain ⟨w, hwa, hwb, hsat⟩ := h
  have hAsat := sat_tableau_of_sat_formula3 e T 𝒟.prog n x y hT hlen hTm w hsat
  set A : TabVar 7 6 Sym Ctl (Sof e) chk.gates.length → Bool :=
    fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ with hAdef
  have hAeq : ∀ v, A v = w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ := fun v => by rw [hAdef]
  obtain ⟨h1, h2, h3, h4⟩ := acceptsIn_of_tableau_sat U Sym.one Sym.zero Sym.one
    (fixedOf 𝒟.prog n T x y) chk A (fun cl hcl => hAsat cl (Or.inl hcl)) chk_isCheckCircuit
    chk_refsLt chk_inputsLt chk_gates_ne
  set inp := inputOf Sym.zero Sym.one (fixedOf 𝒟.prog n T x y) chk A with hinp
  -- the two free tapes hold strings over `{0, 1}`
  have hbits : ∀ jt : Fin 7, fixedOf 𝒟.prog n T x y jt = none →
      bits (boolsOf (inp jt)) = inp jt := fun jt hjt => bits_boolsOf _ (h2 jt hjt)
  have hbits5 : bits (boolsOf (inp 5)) = inp 5 := hbits 5 (by simp [fixedOf])
  have hbits6 : bits (boolsOf (inp 6)) = inp 6 := hbits 6 (by simp [fixedOf])
  -- the strings are short, by the answer-end clauses
  have hshort : ∀ jt : Fin 7, ((jt : ℕ) = 5 ∨ (jt : ℕ) = 6) → (inp jt).length ≤ T := by
    intro jt hjt
    have hpos : T + 3 < numCells (Sof e) := by unfold numCells; omega
    have hclmem : unit (.cell 0 (.inl jt) ⟨T + 3, hpos⟩ CellVal.blank) true ∈
        tableauPlus e T (fixedOf 𝒟.prog n T x y) chk :=
      Or.inr ⟨jt, ⟨T + 3, hpos⟩, hjt, rfl, rfl⟩
    have hval := (unit_eval A _ true).mp (hAsat _ hclmem)
    rw [h3 jt ⟨T + 3, hpos⟩ CellVal.blank] at hval
    have hbl := (of_decide_eq_true hval).symm
    have hle := length_le_of_inputCellVal_blank (inp jt) (⟨T + 3, hpos⟩ : Pos (Sof e))
      (by rw [isBdry_iff]; simp only [Fin.val_mk]; omega) (by simp) hbl
    simpa using hle
  -- the answer blocks are the tape encodings of the strings
  have hans : ∀ (jt : Fin 7) (k : ℕ) (hk : k < 4 * T), (jt : ℕ) = tapeIdx T k →
      bits (boolsOf (inp jt)) = inp jt →
      w ⟨k, by omega⟩ = tapeBits (boolsOf (inp jt)) (rOf T k) := by
    intro jt k hk hjt hbj
    obtain ⟨jt', p, hjt', hp, hdec⟩ := decodeVar_ans e Gc T hT hk
    have hjj : jt' = jt := Fin.ext (by rw [hjt', hjt])
    have hidx : idxOf e Gc T (.cell 0 (.inl jt') p (valOf T k)) = k :=
      idxOf_ans e Gc T hT hk hjt' hp
    have hAv : A (.cell 0 (.inl jt') p (valOf T k)) = w ⟨k, by omega⟩ := by
      rw [hAeq]
      congr 1
      simp only [Fin.mk.injEq]
      exact hidx
    have hk2 : rOf T k < 2 * Sof e := by have := rOf_lt T k hk; omega
    have hcell : inputCellVal (inp jt) p = inputCellVal (bits (boolsOf (inp jt))) p := by
      rw [hbj]
    rw [← hAv, h3 jt' p (valOf T k), hjj, hcell, valOf]
    exact decide_val_inputCellVal e _ (rOf T k) (by rw [hp]) hk2
  -- the machine's inputs are the strings read off the time-`0` rows
  have huinp : uInput 𝒟.prog n T x y (boolsOf (inp 5)) (boolsOf (inp 6)) = inp := by
    funext j
    fin_cases j
    · exact (h1 0 (S 𝒟.prog.toData) (by simp [fixedOf])).symm
    · exact (h1 1 (S (encode n)) (by simp [fixedOf])).symm
    · exact (h1 2 (List.replicate T Sym.one) (by simp [fixedOf])).symm
    · exact (h1 3 (S (encode x)) (by simp [fixedOf])).symm
    · exact (h1 4 (S (encode y)) (by simp [fixedOf])).symm
    · exact hbits5
    · exact hbits6
  refine ⟨boolsOf (inp 5), boolsOf (inp 6), by simpa using hshort 5 (Or.inl rfl),
    by simpa using hshort 6 (Or.inr rfl), ?_, ?_, ?_⟩
  · intro j
    have hrj : rOf T (j : ℕ) = (j : ℕ) := by unfold rOf; rw [if_pos (by omega)]
    have h5 : ((5 : Fin 7) : ℕ) = tapeIdx T (j : ℕ) := by
      unfold tapeIdx; rw [if_pos (by omega)]; rfl
    rw [← hwa j, hans 5 (j : ℕ) (by omega) h5 hbits5, hrj]
  · intro j
    have hrj : rOf T (2 * T + (j : ℕ)) = (j : ℕ) := by
      unfold rOf
      rw [if_neg (by omega)]
      omega
    have h6 : ((6 : Fin 7) : ℕ) = tapeIdx T (2 * T + (j : ℕ)) := by
      unfold tapeIdx; rw [if_neg (by omega)]; rfl
    rw [← hwb j, hans 6 (2 * T + (j : ℕ)) (by omega) h6 hbits6, hrj]
  · refine acceptsWithin_of_accepts 𝒟 n x y _ _ T (by simpa using hshort 5 (Or.inl rfl))
      (by simpa using hshort 6 (Or.inr rfl)) (Sof e) ?_
    rw [huinp]
    exact h4
end MIPRE.TM.CookLevin.Desc
