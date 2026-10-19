-- Prove2me | solution 1 for MIPRE.TM.CookLevin.sat_window
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:29:36.579238+00:00
-- url     : https://prove2.me/submissions/eb718519-9240-4e17-8555-97247246012d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sound.lean (solution of MIPRE.TM.CookLevin.sat_window);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Theorems.Thm_MIPRE_SAT_Circuit_tseitin_values
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_congr

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem eval_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : C.eval x = C.eval x' := by
  unfold eval
  split_ifs
  · rfl
  · exact valueAt_congr C hin x x' hx _
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
/-- Soundness: a satisfying assignment of the formula agreeing with `x` on the inputs
witnesses `C(x) = 1`. -/
theorem eval_of_tseitin_sat (C : Circuit) (hC : C.RefsLt) (hin : C.InputsLt) (hne : C.gates ≠ [])
    (inp gv : ℕ → V) (x : ℕ → Bool) (w : V → Bool) (hx : ∀ i < C.inputs, w (inp i) = x i)
    (hSat : (C.tseitin inp gv).Sat w) : C.eval x = true := by
  have hout := hSat _ (Or.inr rfl)
  simp only [Clause3.eval, cl, Lit.eval, ite_true, Bool.or_self] at hout
  have hlen : 0 < C.gates.length := List.length_pos_iff.mpr hne
  have := tseitin_values C hC inp gv w hSat (C.gates.length - 1) (by omega)
  rw [eval_congr C hin x (fun i => w (inp i)) (fun i hi => (hx i hi).symm)]
  simp only [eval, hne, ite_false]
  rw [← this, hout]
end
end MIPRE.SAT.Circuit

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

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}
/-- The bits of the window read from `f` are the values of `f` on the circuit's inputs. -/
theorem getD_winBits (f : TabVar i w Symbol State S G → Bool) (h0 : f (.emitted 0) = false)
    (t : Fin S) (js : Tape i w → Center S) (n : ℕ) :
    (winBits fun v => f (winVarOf (G := G) t js v)).getD n false = f (inpOf (G := G) t js n) := by
  unfold winBits inpOf
  by_cases h : n < winCard i w Symbol State
  · rw [dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [dif_neg h, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
    simp [h0]
end
end MIPRE.TM.CookLevin

namespace MIPRE.TM.CookLevin
section
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat
theorem sat_emitted_zero : a (.emitted 0) = false :=
  (unit_eval _ _ _).mp (hSat _ (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl rfl)))))))))
end
end MIPRE.TM.CookLevin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin
open Turing SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat
theorem _root_.solution (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
    (hne : chk.gates ≠ []) (t : Fin S) (js : Tape i w → Center S) :
    checkPred M acc (fun v => a (winVarOf (G := chk.gates.length) t js v)) := by
  have hts : (chk.tseitin (inpOf (G := chk.gates.length) t js) (auxOf t js)).Sat a :=
    fun c hc => hSat c (Or.inr ⟨t, js, hc⟩)
  have heval := Circuit.eval_of_tseitin_sat chk hC hin hne _ _
    (fun n => a (inpOf (G := chk.gates.length) t js n)) a (fun _ _ => rfl) hts
  have hfun : (fun n => (winBits fun v => a (winVarOf (G := chk.gates.length) t js v)).getD n false) =
      fun n => a (inpOf (G := chk.gates.length) t js n) :=
    funext (getD_winBits _ (sat_emitted_zero M s₀ s₁ fixed chk a hSat) t js)
  have := hchk (fun v => a (winVarOf (G := chk.gates.length) t js v))
  unfold Circuit.evalBits at this
  rw [hfun] at this
  exact this.mp heval
end MIPRE.TM.CookLevin
