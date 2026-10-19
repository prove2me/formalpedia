-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.litFieldsR_ev
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:31:53.534442+00:00
-- url     : https://prove2.me/submissions/af5df04b-4679-4856-a617-49b646ee22a7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FieldProg.lean (solution of MIPRE.TM.CookLevin.Desc.litFieldsR_ev);
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
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
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
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_dblR_spec
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_apply
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_nbitsR_const

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem getD_bits (k : ℕ) (i : ℕ) : k.bits.getD i false = k.testBit i := by
  rw [Nat.testBit_eq_inth]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem getD_false_cons (bs : BitStr) (k : ℕ) (h : ∀ i, bs.getD i false = k.testBit i) :
    ∀ i, (false :: bs).getD i false = (2 * k).testBit i := by
  intro i
  cases i with
  | zero => rw [List.getD_cons_zero, Nat.testBit_zero]; simp [Nat.mul_mod_right]
  | succ i =>
    rw [List.getD_cons_succ, h i, Nat.testBit_succ]
    congr 1
    omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
theorem cstR_apply {w : PolyTimeFun ι Unary} {bs : PolyTimeFun ι BitStr} {i : ι} (k : ℕ)
    (h : ∀ j, (bs i).getD j false = k.testBit j) : cstR w bs i = cst (w i).length k := by
  rw [cstR, ap₁_apply, nbitsR_apply k h, constBitsP_apply, cst, nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
theorem bitsR_spec (k : ℕ) (i : ι) : ∀ j, ((bitsR k : PolyTimeFun ι BitStr) i).getD j false =
    k.testBit j := getD_bits k
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
theorem cstR_zero (w : PolyTimeFun ι Unary) (i : ι) :
    cstR w (bitsR 0) i = cst (w i).length 0 := cstR_apply 0 (bitsR_spec 0 i)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
theorem cstR_const (w : PolyTimeFun ι Unary) (k : ℕ) (i : ι) :
    cstR w (bitsR k) i = cst (w i).length k := cstR_apply k (bitsR_spec k i)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
theorem quadR_spec (T : PolyTimeFun ι ℕ) (i : ι) :
    ∀ j, (quadR T i).getD j false = (4 * T i).testBit j := by
  intro j
  have h := getD_false_cons _ _ (dblR_spec T i) j
  rw [show 2 * (2 * T i) = 4 * T i by ring] at h
  exact h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem flagR_apply (i : ι) : flagR eu b i = flagF (eu i).length Gc (b i).length := by
  rw [flagR, ap₁_apply, Fml.inpF_apply, offR_apply, length_flagOffU, flagF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem jR_apply (i : ι) : jR eu b i = jF (eu i).length Gc (b i).length := by
  rw [jR, ap₂_apply, fieldP_apply, ap₁_apply, unaryToBin_apply, length_flagOffU, jF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem twoTbR_apply (i : ι) : twoTbR eu TR i = twoTb (eu i).length Gc (TR i) := by
  rw [twoTbR, nbitsR_apply _ (dblR_spec TR i), length_flagOffU, twoTb]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem lt2TR_apply (i : ι) : lt2TR eu TR b i = lt2TF (eu i).length Gc (TR i) (b i).length := by
  rw [lt2TR, ap₂_apply, ltConstP_apply, jR_apply, twoTbR_apply, lt2TF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem rR_apply (i : ι) : rR eu TR b i = rF (eu i).length Gc (TR i) (b i).length := by
  rw [rR, ap₃_apply, muxListP_apply, ap₂_apply, subConstBitsP_apply, lt2TR_apply, jR_apply,
    twoTbR_apply, rF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem pAnsR_apply (i : ι) : pAnsR eu TR b i = pAnsF (eu i).length Gc (TR i) (b i).length := by
  rw [pAnsR, ap₂_apply, addConstBitsP_apply, ap₂_apply, take_apply, ap₁_apply, tail_apply,
    rR_apply, nbitsR_const, length_WU, pAnsF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem tagR_apply (i : ι) : tagR eu b i =
    muxList (flagF (eu i).length Gc (b i).length) (Fml.field ((b i).length + tagOff) 3)
      (cst 3 0) := by
  simp only [tagR, ap₃_apply, muxListP_apply, ap₂_apply, ap₁_apply, fieldP_apply,
    unaryToBin_apply, cstR_zero, length_threeU, flagR_apply, tagOff, Nat.add_zero]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem tR_apply (i : ι) : tR eu b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + tOff) (W (eu i).length)) (cst (W (eu i).length) 0) := by
  simp only [tR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_threeU, length_WU, flagR_apply, tOff]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem dR_apply (i : ι) : dR eu TR b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + dOff (eu i).length) 4)
      (muxList (lt2TF (eu i).length Gc (TR i) (b i).length) (cst 4 5) (cst 4 6)) := by
  simp only [dR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_const,
    length_fourU, length_dOffU, flagR_apply, lt2TR_apply]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem pR_apply (i : ι) : pR eu TR b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + pOff (eu i).length) (W (eu i).length))
      (pAnsF (eu i).length Gc (TR i) (b i).length) := by
  simp only [pR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, length_WU,
    length_pOffU, flagR_apply, pAnsR_apply]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem vR_apply (i : ι) : vR eu TR b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + vOff (eu i).length) 3)
      (muxList ((rF (eu i).length Gc (TR i) (b i).length).headD (Fml.const false)) (cst 3 1)
        (cst 3 5)) := by
  simp only [vR, ap₃_apply, muxListP_apply, ap₂_apply, ap₁_apply, fieldP_apply, offR_apply,
    cstR_const, length_threeU, length_vOffU, flagR_apply, headD_apply, rR_apply]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem qR_apply (i : ι) : qR eu b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + qOff (eu i).length) Qb) (cst Qb 0) := by
  simp only [qR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_QbU, length_qOffU, flagR_apply]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem jsR_apply (k : ℕ) (i : ι) : jsR eu b k i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + jsOff (eu i).length k) (W (eu i).length))
      (cst (W (eu i).length) 0) := by
  simp only [jsR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_WU, length_jsOffU, flagR_apply]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem gR_apply (i : ι) : gR eu b i =
    muxList (flagF (eu i).length Gc (b i).length)
      (Fml.field ((b i).length + gOff (eu i).length) (Gb Gc)) (cst (Gb Gc) 0) := by
  simp only [gR, ap₃_apply, muxListP_apply, ap₂_apply, fieldP_apply, offR_apply, cstR_zero,
    length_GbU, length_gOffU, flagR_apply]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem ansOkR_apply (i : ι) : ansOkR eu TR b i =
    Fml.and (Fml.not (flagF (eu i).length Gc (b i).length))
      (Fml.ltConst (jF (eu i).length Gc (b i).length)
        (nbits (flagOff (eu i).length Gc) (4 * TR i))) := by
  have hquad : nbitsR (flagOffU eu) (quadR TR) i =
      nbits (flagOff (eu i).length Gc) (4 * TR i) := by
    rw [nbitsR_apply _ (quadR_spec TR i), length_flagOffU]
  simp only [ansOkR, ap₂_apply, ap₁_apply, Fml.andF_apply, Fml.notF_apply, ltConstP_apply,
    flagR_apply, jR_apply, hquad]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
variable (eu : PolyTimeFun ι Unary) (TR : PolyTimeFun ι ℕ) (b : PolyTimeFun ι Unary)
theorem _root_.solution (i : ι) :
    (litFieldsR eu TR b).ev i = litFields (eu i).length Gc (TR i) (b i).length := by
  simp only [FieldsR.ev, litFieldsR, litFields, FieldsF.mk.injEq]
  exact ⟨flagR_apply eu b i, tagR_apply eu b i, tR_apply eu b i, dR_apply eu TR b i,
    pR_apply eu TR b i, vR_apply eu TR b i, qR_apply eu b i, funext fun k => jsR_apply eu b k i,
    gR_apply eu b i, ansOkR_apply eu TR b i⟩
end MIPRE.TM.CookLevin.Desc
