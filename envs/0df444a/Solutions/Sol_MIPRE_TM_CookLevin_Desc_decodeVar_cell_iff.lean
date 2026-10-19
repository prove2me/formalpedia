-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.decodeVar_cell_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:41.122052+00:00
-- url     : https://prove2.me/submissions/b7f730df-f0d4-4dee-bb11-8140b7684a22

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Kinds.lean (solution of MIPRE.TM.CookLevin.Desc.decodeVar_cell_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem symOfCode_symCode (v : CellVal Sym) : symOfCode (symCode v) = some v := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem symCode_lt (v : CellVal Sym) : symCode v < 7 := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> decide
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem symOfCode_eq_some {k : ℕ} {v : CellVal Sym} (h : symOfCode k = some v) : symCode v = k := by
  match k, h with
  | 0, h => cases h; rfl
  | 1, h => cases h; rfl
  | 2, h => cases h; rfl
  | 3, h => cases h; rfl
  | 4, h => cases h; rfl
  | 5, h => cases h; rfl
  | 6, h => cases h; rfl
  | n + 7, h => simp [symOfCode] at h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem tapeOfCode_tapeCode (d : Tape 7 6) : tapeOfCode (tapeCode d) = some d := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩
  · simp [tapeOfCode, tapeCode, hj]
  · show tapeOfCode (7 + j) = _
    unfold tapeOfCode
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    ext
    simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem tapeOfCode_eq_some {k : ℕ} {d : Tape 7 6} (h : tapeOfCode k = some d) : tapeCode d = k := by
  unfold tapeOfCode at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; simp [tapeCode]; omega
    · cases h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem tape_eq_inl_of_lt (d : Tape 7 6) (h : tapeCode d < 7) : d = .inl ⟨tapeCode d, h⟩ := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩
  · rfl
  · simp [tapeCode] at h
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open SAT Cost Fml
variable (e G : ℕ)
theorem _root_.solution (F : Fields) (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e))
    (v : CellVal Interp.Sym) :
    decodeVar e G F = some (.cell t d p v) ↔
      IsCell e F ∧ F.t = t ∧ F.d = tapeCode d ∧ F.p = p ∧ F.v = symCode v := by
  constructor
  · intro h
    unfold decodeVar at h
    split at h
    · rename_i hflag
      split at h
      · rename_i htag
        split at h
        · rename_i hb
          split at h
          · rename_i d' v' hd hv
            cases h
            have hd' := tapeOfCode_eq_some hd
            have hv' := symOfCode_eq_some hv
            refine ⟨Or.inl ⟨hflag, htag, hb.1, ?_, hb.2, ?_⟩, rfl, hd'.symm, rfl, hv'.symm⟩
            · rw [← hd']; exact tapeCode_lt _
            · rw [← hv']; exact symCode_lt _
          · cases h
        · cases h
      · exfalso; split_ifs at h <;> (try split at h) <;> cases h
    · rename_i hflag
      split at h
      · rename_i hok
        split at h
        · rename_i hb
          split at h
          · rename_i v' hv
            cases h
            have hv' := symOfCode_eq_some hv
            refine ⟨Or.inr ⟨by simpa using hflag, hok.1, hok.2.1, hok.2.2, hb.1, hb.2, ?_⟩,
              by rw [hok.2.2]; rfl, by simp [tapeCode], rfl, hv'.symm⟩
            rw [← hv']; exact symCode_lt _
          · cases h
        · cases h
      · cases h
  · rintro ⟨hk, ht, hd, hp, hv⟩
    unfold decodeVar
    rcases hk with ⟨hf, htag, hb1, hb2, hb3, hb4⟩ | ⟨hf, hok, htag, ht0, hb2, hb3, hb4⟩
    · rw [if_pos hf, if_pos htag, dif_pos ⟨hb1, hb3⟩, hd, hv, tapeOfCode_tapeCode, symOfCode_symCode]
      simp only [Option.some.injEq]
      congr 1 <;> ext <;> simp [ht, hp]
    · rw [if_neg (by simp [hf]), if_pos ⟨hok, htag, ht0⟩, dif_pos ⟨hb2, hb3⟩, hv, symOfCode_symCode]
      simp only [Option.some.injEq]
      have hd' : d = .inl ⟨tapeCode d, by omega⟩ := tape_eq_inl_of_lt d (by omega)
      rw [hd']
      congr 1
      · ext; simp [← ht, ht0]
      · congr 1; ext; simp [hd]
      · ext; simp [hp]
end MIPRE.TM.CookLevin.Desc
