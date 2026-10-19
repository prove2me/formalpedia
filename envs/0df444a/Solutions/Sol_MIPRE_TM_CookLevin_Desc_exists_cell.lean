-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.exists_cell
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:49.703536+00:00
-- url     : https://prove2.me/submissions/67849f10-8c96-4a7b-b4ad-fd6029dc91d7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Families.lean (solution of MIPRE.TM.CookLevin.Desc.exists_cell);
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
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_cell_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open Interp SAT Cost
variable (e G : ℕ)
theorem tapeOfCode_of_lt {k : ℕ} (h : k < 13) : ∃ d, tapeOfCode k = some d := by
  unfold tapeOfCode
  split_ifs <;> exact ⟨_, rfl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem symOfCode_of_lt {k : ℕ} (h : k < 7) : ∃ v, symOfCode k = some v := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | exact ⟨_, rfl⟩ | omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
variable (e G : ℕ)
theorem _root_.solution {F : Fields} (h : IsCell e F) :
    ∃ (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym),
      decodeVar e G F = some (.cell t d p v) := by
  rcases h with ⟨hf, htag, ht, hd, hp, hv⟩ | ⟨hf, hok, htag, ht, hd, hp, hv⟩
  · obtain ⟨d, hd'⟩ := tapeOfCode_of_lt hd
    obtain ⟨v, hv'⟩ := symOfCode_of_lt hv
    exact ⟨⟨F.t, by omega⟩, d, ⟨F.p, hp⟩, v, (decodeVar_cell_iff e G F _ _ _ _).mpr
      ⟨Or.inl ⟨hf, htag, ht, hd, hp, hv⟩, rfl, (tapeOfCode_eq_some hd').symm, rfl,
        (symOfCode_eq_some hv').symm⟩⟩
  · obtain ⟨d, hd'⟩ := tapeOfCode_of_lt (by omega : F.d < 13)
    obtain ⟨v, hv'⟩ := symOfCode_of_lt hv
    exact ⟨⟨F.t, by omega⟩, d, ⟨F.p, hp⟩, v, (decodeVar_cell_iff e G F _ _ _ _).mpr
      ⟨Or.inr ⟨hf, hok, htag, ht, hd, hp, hv⟩, rfl, (tapeOfCode_eq_some hd').symm, rfl,
        (symOfCode_eq_some hv').symm⟩⟩
end MIPRE.TM.CookLevin.Desc
