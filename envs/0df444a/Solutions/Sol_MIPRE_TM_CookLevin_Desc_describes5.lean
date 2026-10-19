-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.describes5
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:54:55.332969+00:00
-- url     : https://prove2.me/submissions/4649a3b9-4e64-4d12-bb33-b238dd1952b0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Decoupled.lean (solution of MIPRE.TM.CookLevin.Desc.describes5);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
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
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_encodesAccepted_of_extendsAnswers
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_extendsAnswers_of_encodesAccepted
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_sat_formula5_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (𝒟 : Decider) (n T : ℕ) (x y : BitStr) (e : ℕ)
/-- **Item 1 of `thm:succinct-sat` for the describer.** -/
theorem extendsAnswers_iff (hT : T ≤ Sof e) (hlen : FixedLen e 𝒟.prog n T x y)
    (hTm : T + 3 < 2 ^ W e)
    (hrb : ∀ ap bp : BitStr, ap.length ≤ T → bp.length ≤ T →
      runBound 𝒟.prog n x y ap bp T ≤ Sof e)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (a b : Fin (2 * T) → Bool) :
    ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)) a b ↔
      EncodesAccepted 𝒟 n x y T a b :=
  ⟨encodesAccepted_of_extendsAnswers 𝒟 n T x y e hT hlen hTm h4T a b,
    extendsAnswers_of_encodesAccepted 𝒟 n T x y e hT hlen hTm hrb h4T a b⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
/-- Past twice the length of the string, a tape block is the blank cell `10`: `true` at even
positions and `false` at odd ones. This is the parity the audit campaign repaired, and it is
what rows 4 to 7 assert. -/
theorem tapeBits_of_ge {s : BitStr} {T p : ℕ} (hs : s.length ≤ T) (hp : 2 * T ≤ p) :
    tapeBits s p = decide (p % 2 = 0) := by
  have hnone : s[p / 2]? = none := List.getElem?_eq_none (by omega)
  rw [tapeBits, hnone]
  rcases Nat.eq_zero_or_pos (p % 2) with h | h
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg (by omega), decide_eq_false (by omega)]
    rfl
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
theorem _root_.solution (𝒟 : Decider) (ℓ T e : ℕ) (n : ℕ) (x y : BitStr)
    (hℓ : 2 * T ≤ 2 ^ ℓ) (hℓr : ℓ ≤ mOf e Gc) (hr : 1 ≤ mOf e Gc)
    (h4T : 4 * T ≤ 2 ^ mOf e Gc) (hTle : T ≤ Sof e)
    (hlen : FixedLen e 𝒟.prog n T x y) (hTm : T + 3 < 2 ^ W e)
    (hrb : ∀ ap bp : BitStr, ap.length ≤ T → bp.length ≤ T →
      runBound 𝒟.prog n x y ap bp T ≤ Sof e) :
    (descCirc5 ℓ T e 𝒟.prog n x y).DescribesDecider ℓ (mOf e Gc) 𝒟 n x y T := by
  have hT : 2 * T < 2 ^ mOf e Gc := by
    rcases Nat.eq_zero_or_pos T with rfl | hTpos
    · simp
    · omega
  have hiff := extendsAnswers_iff 𝒟 n T x y e hTle hlen hTm hrb h4T
  intro a b
  constructor
  · rintro ⟨w₁, w₂, w₃, hsat⟩
    obtain ⟨htri, hlink⟩ :=
      (sat_formula5_iff ℓ T e 𝒟.prog n x y hℓr hr hT hTle hlen hTm a b w₁ w₂ w₃).mp hsat
    have h12 : ∀ i, w₁ i = w₂ i := fun i => hlink.w12 i i rfl
    have h23 : ∀ i, w₂ i = w₃ i := fun i => hlink.w23 i i rfl
    have e12 : w₁ = w₂ := funext h12
    have e23 : w₂ = w₃ := funext h23
    have hsat3 : ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc)).Sat w₁ := by
      intro c₃ hc₃
      have h := htri c₃ hc₃
      rw [← e23, ← e12] at h
      exact h
    have hext : ExtendsAnswers h4T ((descCirc e T 𝒟.prog n x y).formula3 (mOf e Gc))
        (fun j : Fin (2 * T) => a ⟨j, by omega⟩) (fun j : Fin (2 * T) => b ⟨j, by omega⟩) := by
      refine ⟨w₁, fun j => ?_, fun j => ?_, hsat3⟩
      · exact (hlink.aLow ⟨j, by omega⟩ ⟨j, by omega⟩ j.isLt rfl).symm
      · exact (hlink.bLow ⟨j, by omega⟩ ⟨2 * T + j, by omega⟩ j.isLt (by simp; omega)).symm
    obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ := hiff _ _ |>.mp hext
    refine ⟨ap, bp, hap, hbp, fun j => ?_, fun j => ?_, hacc⟩
    · rcases lt_or_ge (j : ℕ) (2 * T) with hj | hj
      · exact ha ⟨j, hj⟩
      · rw [hlink.aPad j (by omega), tapeBits_of_ge hap hj]
    · rcases lt_or_ge (j : ℕ) (2 * T) with hj | hj
      · exact hb ⟨j, hj⟩
      · rw [hlink.bPad j (by omega), tapeBits_of_ge hbp hj]
  · rintro ⟨ap, bp, hap, hbp, ha, hb, hacc⟩
    obtain ⟨w, hw1, hw2, hsat3⟩ := hiff (fun j : Fin (2 * T) => a ⟨j, by omega⟩)
      (fun j : Fin (2 * T) => b ⟨j, by omega⟩) |>.mpr
      ⟨ap, bp, hap, hbp, fun j => by simpa using ha ⟨j, by omega⟩,
        fun j => by simpa using hb ⟨j, by omega⟩, hacc⟩
    refine ⟨w, w, w, ?_⟩
    rw [sat_formula5_iff ℓ T e 𝒟.prog n x y hℓr hr hT hTle hlen hTm a b w w w]
    refine ⟨fun c₃ hc₃ => hsat3 c₃ hc₃, ⟨?_, ?_, ?_, ?_, fun i j hij => ?_, fun i j hij => ?_⟩⟩
    · intro i j hi hij
      have h := hw1 ⟨(i : ℕ), hi⟩
      calc a i = a ⟨(i : ℕ), by omega⟩ := rfl
        _ = w ⟨(i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext hij)
    · intro i j hi hij
      have h := hw2 ⟨(i : ℕ), hi⟩
      calc b i = b ⟨(i : ℕ), by omega⟩ := rfl
        _ = w ⟨2 * T + (i : ℕ), by omega⟩ := h.symm
        _ = w j := congrArg w (Fin.ext (by simp; omega))
    · intro i hi
      rw [ha i, tapeBits_of_ge hap (by omega)]
    · intro i hi
      rw [hb i, tapeBits_of_ge hbp (by omega)]
    · exact congrArg w (Fin.ext hij)
    · exact congrArg w (Fin.ext hij)
end MIPRE.TM.CookLevin.Desc
