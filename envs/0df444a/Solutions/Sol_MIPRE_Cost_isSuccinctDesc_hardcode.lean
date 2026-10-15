-- Prove2me | solution 1 for MIPRE.Cost.isSuccinctDesc_hardcode
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:53:02.513952+00:00
-- url     : https://prove2.me/submissions/5f2bca86-25a1-4910-bc40-db9dc1afa068

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Succinct.lean (solution of MIPRE.Cost.isSuccinctDesc_hardcode);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Theorems.Thm_MIPRE_Cost_Prog_bitQueryProg_runs
import Theorems.Thm_MIPRE_Cost_hardcode_time

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem size_ofBool (b : Bool) : (ofBool b).size ≤ 3 := by cases b <;> simp [ofBool]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem size_ofList_le {α : Type*} {f : α → Data} {B : ℕ} (hf : ∀ a, (f a).size ≤ B)
    (l : List α) : (ofList f l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    have := hf a
    simp only [ofList, size_cons, List.length_cons, Nat.mul_succ]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost
theorem esize_bitStr_le (x : BitStr) : esize x ≤ 4 * x.length + 1 :=
  Data.size_ofList_le Data.size_ofBool x
end MIPRE.Cost

namespace MIPRE.Cost
theorem esize_nat_le (n : ℕ) : esize n ≤ 4 * Nat.size n + 1 := by
  have := esize_bitStr_le n.bits
  rw [Nat.size_eq_bits_len] at this
  exact this
end MIPRE.Cost

namespace MIPRE.Cost.Prog
theorem revOntoBody_wellScoped : revOntoBody.WellScoped 1 := by
  simp [revOntoBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem revOntoProg_wellScoped : revOntoProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, revOntoBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroBody_wellScoped : isZeroBody.WellScoped 1 := by
  simp [isZeroBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroProg_wellScoped : isZeroProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, isZeroBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decProg_wellScoped : decProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, decBody_wellScoped.mono (by omega) _⟩,
      revOntoProg_wellScoped.mono (by omega) _⟩⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem bitAtBody_wellScoped : bitAtBody.WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, ⟨trivial, trivial⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) isZeroProg_wellScoped, ?_⟩
  refine ⟨by decide, ⟨trivial, by simp [WellScoped]⟩, ⟨trivial, trivial⟩,
    ⟨by simp [WellScoped], ?_⟩⟩
  exact callVar_wellScoped (by decide) decProg_wellScoped
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem bitAtProg_wellScoped : bitAtProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitAtBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost
open Polynomial
theorem hardcode_wellScoped {p : Prog} (hp : p.WellScoped 1) (d : Data) :
    (hardcode p d).WellScoped 1 :=
  ⟨⟨trivial, Nat.zero_lt_one⟩, hp.mono (by omega) _⟩
end MIPRE.Cost

namespace MIPRE.Cost.Prog
open Polynomial
theorem bitQueryProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (bitQueryProg univ).WellScoped 1 :=
  ⟨by decide, trivial, by decide, trivial, by decide, trivial,
    ⟨by simp [WellScoped], by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) hU,
    ⟨by simp [WellScoped], by simp [WellScoped]⟩,
    callVar_wellScoped (by decide) bitAtProg_wellScoped⟩
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n' : α) (n : ℕ) (y : BitStr)
    {t : ℕ} (hrun : c'.Runs (encode (e, n')) (encode y) t) (hlen : t ≤ 2 ^ n)
    (hbudget : (bitQueryBound U).eval (esize c' + esize e + esize n' + t) +
      (esize c' + esize e + 1 + esize n' + 1) + 4 ≤ n + 1) :
    IsSuccinctDesc (hardcode (Prog.bitQueryProg U.univ) (encode ((c', e), n'))) n y := by
  refine ⟨hardcode_wellScoped (Prog.bitQueryProg_wellScoped U.closed) _, ?_, fun m => ?_⟩
  · exact (length_le_esize_bitStr y).trans (hrun.size_le.trans hlen)
  · obtain ⟨T, hT, h⟩ := Prog.bitQueryProg_runs U c' e n' y m hrun
    refine ⟨T + (encode ((c', e), n')).size + (encode m).size + 3, ?_,
      hardcode_time (Prog.bitQueryProg_wellScoped U.closed) h⟩
    have hd : (encode ((c', e), n')).size = esize c' + esize e + 1 + esize n' + 1 := rfl
    have hsm : (encode m).size ≤ 4 * Nat.size m + 1 := esize_nat_le m
    have hP1 : Nat.size m + 1 ≤ (Nat.size m + 1) ^ 2 := by
      rw [pow_two]; exact Nat.le_mul_self _
    have hmul := Nat.mul_le_mul_right ((Nat.size m + 1) ^ 2) hbudget
    have hexp : ((bitQueryBound U).eval (esize c' + esize e + esize n' + t) +
        (esize c' + esize e + 1 + esize n' + 1) + 4) * (Nat.size m + 1) ^ 2 =
        (bitQueryBound U).eval (esize c' + esize e + esize n' + t) * (Nat.size m + 1) ^ 2 +
        (esize c' + esize e + 1 + esize n' + 1) * (Nat.size m + 1) ^ 2 +
        4 * (Nat.size m + 1) ^ 2 := by ring
    have hle : esize c' + esize e + 1 + esize n' + 1 ≤
        (esize c' + esize e + 1 + esize n' + 1) * (Nat.size m + 1) ^ 2 :=
      Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) 2)
    omega
